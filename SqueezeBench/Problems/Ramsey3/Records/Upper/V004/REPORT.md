# Ramsey3, upper record, V004

By trial claude-fable.

## How the bound was obtained

A second level of the deletion argument of V003, in a form that depends only on `n` and
`D = k - 1`. Let `G` be triangle-free on `n` vertices with all degrees at most `D` and no
independent `(D+1)`-set, and let `v` be a vertex whose neighbours have the largest total degree
`s_v = Σ_{w ∈ N(v)} deg w`. Then `s_v ≥ Σ_w deg w² / n ≥ (Σ deg)² / n²`, so the graph
`G - N[v]` has `m' ≥ m := n - 1 - D` vertices and degree sum `σ = Σ deg - 2 s_v ≤ X := D (n - 2D)`.
The V003 identity applied inside `G - N[v]` — the sum over its vertices `u` of the local bounds
`1 + a |W_u| - β · 2e(W_u)` equals `Σ_y (1 + a (m' - 1 - d_y) - β d_y (m' - 2 d_y))` — with
Cauchy–Schwarz `Σ d_y² ≥ σ²/m'` in place of the per-vertex minimisation gives an independent set
of size at least `q(m', σ/m')`, `q(m, x) = 1 + a (m - 1 - x) - β x (m - 2x)`, and `q` is
decreasing in `x` for `x ≤ m/4` and increasing in `m`, so `α(G) ≥ 1 + q(m, X/m)` whenever
`n ≥ 5D + 1`. Here `a = f(r) + r β`, `β = f(r) - f(r+1)` for a secant point `r`, as in V003.

If `1 + q(m, X/m) > D` at `n = N₀` then every graph on at least `N₀` vertices forces (restrict
to an induced subgraph on exactly `N₀` vertices), so no monotonicity in `n` is needed. The record
therefore only *checks* a certificate: `check D r N₀` is the inequality
`A m² (m-1) + 2 B X² > (D-2) q(r+1) m² + B X m² + A m X` in ℕ (the denominators `q(r+1)` and
`m²` cleared, `A = q(r+1) a`, `B = q(r+1) β` as in V003), together with `2 ≤ D`,
`5D + 1 ≤ N₀` and the slope condition `B D < A`; `v k` is the least of `V - 3, V - 2, V - 1`
(`V` the V003 value) certified by some `r < k`, else `V`.

Compared with V003 this gains the convexity of `f` at the second deletion: `1` at
`k = 12, 14, 17, 19–38, 40, 80`, `2` at `k = 39, 50, 60, 100` (and `0` at the other `k ≤ 40`).
A full two-level argument with the exact second moments of the codegrees was computed to give
the same values in the regular case, so nothing is lost by the Jensen form, and the gains stay
second order (`O(log k)` in `n`).

The refinement was designed by the AI agent named below after quantifying, with exact rational
arithmetic in Python, that the one-level bound of V003 is tight for `D`-regular graphs and that
a second level gains one or two; the same script tabulated the certificates.

## How the proofs were obtained

Written by hand in Lean, on top of V002 and V003: `avg_bound` (the V003 identity plus
Cauchy–Schwarz, `sq_sum_le_card_mul_sum_sq`), `sum_deg_non_vertex` (the degree sum of
`G - N[v]`, from `card_nbr_non`, `sum_split` and `count_walks`), `q_mono` and `sigma_le`
(pure ℚ inequalities, proved with explicit product hints and `linarith`), `check_arith`
(the ℕ encoding against the ℚ inequality), `q_le_of_ramsey` (the graph part, which chooses `v`
by `Finset.exists_max_image` and restricts to a subset of exactly `N₀` vertices with
`Finset.exists_subset_card_eq`) and the wrapper `forcesOn_check`.

One lesson worth recording: the first version of the wrapper kept the huge ℕ certificate
inequality in the context while calling `omega` and `linarith`, and cost 145000 heartbeats;
moving the graph argument into a lemma that never sees the certificate brought the whole file
to 67876 (limit 200000). Heaviest declaration `q_le_of_ramsey` at 31453.

## Setup

- Tools: Claude Fable 5.1 (Claude Code) as the submitter; two consultations of GPT-6 Astra (the
  second one confirmed that no known search-free refinement gains more than lower-order terms).
  Lean 4.31.0, Mathlib as pinned by the project. Python with exact fractions to tabulate the
  bound and the certificates.
- Machine: 96 cores, 755 GB memory, Linux 6.8.0-124-generic.
- Time spent: about two hours.
