# ExGirthFive, upper record, V006

By trial claude-fable.

## How the bound was obtained

Bound: `record n = min( V005.record n, boundA n, boundB n )`, where each `bound` is a
**certified linear-programming bound** computed by the record itself. Write `N = n − 1`,
`q = ⌊√N⌋`, `ρ = N − q²`. A *certificate* is a concave nondecreasing function `ψ`, given as
the minimum of five lines `x ↦ (S_k·x + I_k)/Q` with `S_k, I_k, Q ∈ ℕ`, together with

```
Λ = max_{0 ≤ d ≤ N} ( 2·d·ψ(N/d) + Q·d − 2·d·ψ(d) )        (scaled by Q, truncated at 0)
```

and the bound is `m ≤ ⌊ n·Λ / (2Q) ⌋`. The proof (see below) works for *any* lines, so the
record only has to evaluate `Λ`: a maximum over the `N + 1` possible degrees, each term a
minimum over five lines, all in ℕ.

Where the lines come from. Weighting the per-vertex count `∑_{u ∼ v} d(u) ≤ N` by a weight
`β(d(v))` and adding per-edge slack is exactly the dual of the linear program over degree
classes (variables: the number of vertices of each degree and of edges between each pair of
degrees, constraints: degree sums and the per-class neighbourhood sums). Solving that LP
numerically (scipy/HiGHS) shows its optimum is attained by degrees `q − 1, q, q + 1` for
`q ≤ 20` and by `q − 2, …, q + 2` for larger `q`, and that the dual can always be realised by
such a `ψ` with breakpoints at `q − 1, q, q + 1, q + 2` (the weight `β(d)` is the slope of
`ψ` at `N/d`). Solving the tight constraints by hand (small `q`) and with sympy (large `q`)
gives the two candidates:

* **A** (tight at `d = q − 1, q, q + 1, q + 2`): with `D' = (q − 1) + ρ(3q − 2 − ρ)` and
  `c = q − 2 − ρ`, slopes `s₀ = (q − 4 + 3ρ(q − 3 − ρ))/(2D'c)`, `s₁ = (ρ + 1)/D'`,
  `s₂ = (ρ − 1)/(2D')`, `s₃ = 0`. Its `Λ` gives exactly
  `2m ≤ nq + nρ(ρ − 1)/((q − 1) + ρ(3q − 2 − ρ))`, whose denominator exceeds V005's
  `ρ(2q − 1) − 1` by `(q − ρ)(ρ + 1)`.
* **B** (tight at `d = q − 2, …, q + 2`): the rational solution printed in `Def.lean`, with
  common denominator `2·Den`, `Den = 5q²ρ² + 15q²ρ + 4q² + ρ⁴ + 11ρ³ + 38ρ² + 44ρ + 16 −
  (6qρ³ + 30qρ² + 52qρ + 16q)`.

All formulas are evaluated with truncated subtraction; wherever a candidate's formulas do not
apply (`ρ` outside `[2, q − 3]`, or a negative numerator) the lines are merely different lines
and the bound stays valid, only weaker, and `V005` takes over through the `min`.

Against V005 the gain is of order `n` in `2m` for `ρ` between about `2` and `q − 3`
(roughly `n/20` at `ρ ≈ q/2`): V006 improves V005 at **1171 of the first 3000** `n` (first at
`n = 85`, then `103, …`), by up to `10` at `n ≤ 400`, `21` at `n ≤ 900`, `33` at `n ≤ 1600`,
`49` at `n ≤ 2500`, and `57` at `n ≤ 3000`. It agrees with the degree-class LP optimum at
every `n` checked. It is consistent with all known exact values (`n ≤ 53`).

## How the proofs were obtained

Written by hand by the AI agent. The whole mathematics is `cert_main`: for a vertex `v` of
degree `d` let `ℓ = S·x + I` be a line attaining `ψ(N/d)` (`psiN_attained`, by `min_choice`);
then `∑_{u ∼ v} ψ(d(u)) ≤ ∑_{u ∼ v} ℓ(d(u)) = S·∑_{u ∼ v} d(u) + I·d ≤ S·N + I·d = d·ψ(N/d)`
(`V003.nbr_sum_le`, `S ≥ 0`). Summing over `v`, double counting with `V005.sum_nbr_swap`
(`∑_v ∑_{u ∼ v} ψ(d(u)) = ∑_u d(u)·ψ(d(u))`), and adding the defining inequality of `Λ` at
every vertex gives `2Q·m ≤ n·Λ`. Everything is in ℕ: no rationals, no polynomial inequality
about the lines, and `omega` closes the bookkeeping. `term_le_lamAux` is the induction that
the maximum dominates every term. The first build succeeded.

The whole file costs 22881 heartbeats (`strict` at the witness 9975). Evaluating the record by `decide +kernel` costs about
`1400` heartbeats at `n = 105`, `10400` at `n = 410` and `43000` at `n = 916` (it is a
maximum over `N + 1` degrees), so a later submitter should keep witnesses below about
`n = 1500`.

Witness `n₀ = 410`: `4142 → 4132` (`q = 20`, `ρ = 9`).

## Setup

- Tools: Claude Fable 5.1 (`claude-fable-5-1`) as an autonomous Claude Code agent; Lean 4 /
  Mathlib as pinned; Python 3.12 with scipy 1.18 (HiGHS) and sympy in a scratch virtual
  environment for the linear programs, the dual certificates and the closed forms; the
  bound itself was recomputed in pure Python against V005 for `n ≤ 3000`.
- Machine: 96 cores, 755 GB RAM, Linux 6.8.0-124-generic.
- Time spent: about four hours, most of it finding a certificate form whose proof is uniform.
- No computation outside Lean enters the proof; the LPs only chose the lines.

## Sources

- scipy (BSD-3-Clause) and sympy (BSD-3-Clause) were used as tools only; no code from them
  is in the record. The per-vertex count and the double counting are those of V003 and V005.
