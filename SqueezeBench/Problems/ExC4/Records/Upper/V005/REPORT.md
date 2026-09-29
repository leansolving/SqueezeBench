# ExC4, upper record, V005

By trial claude-fable.

## How the bound was obtained

The bound is a *weighted local count* certified per `n` by data in `Def.lean`.

**The local count.** For a vertex `x` of a `C₄`-free graph let `s(x) = Σ_{y ∈ N(x)} (d(y) − 1)`.
The sets `N(y) \ {x}` for `y ∈ N(x)` are pairwise disjoint (two of them meeting in `z` would
give `x` and `z` two common neighbours), they are disjoint from the set of neighbours of `x`
that share no neighbour with `x`, and all these sets lie among the other `n − 1` vertices.
Since the edges inside `N(x)` form a matching, a vertex of odd degree has such a lone
neighbour (V003's `card_mset_le`). Hence, for every vertex,

```
s(x) + (d(x) mod 2)  ≤  n − 1.                                             (L)
```

V003 uses only the sum of (L) over all vertices. Summing it with a *weight depending on the
degree* is strictly stronger: a vertex of high degree needs neighbours of low degree, and
a linear program over degree classes (variables: the number of vertices of each degree and
the number of edges between each pair of degree classes, constraints: the sum of (L) over each
class) beats V004 at about 55% of all `n ≤ 300`.

**The certificate.** A certificate for `n` is a target `B`, a degree `k`, a list of weights
`ls` (scaled by `M = 2²⁰`) for the degrees `k, k+1, …`, and implicitly the scaled target
`β = ⌊(2M(B+1) − 1)/n⌋` and the tail weight `g = ⌊β/(n−1)⌋`. It defines a weight `w(i)` for
every degree (`0` below `k`, the list from `k` on, `g` beyond the list) and an offset `δ(i)`
(the largest value allowed by (D1) below `T = k + |ls|`, and `(i−1)g − M` beyond). The record
checks, for the finitely many degrees `i < T` and pairs `i < j ≤ T`,

```
(D1)  M·i + w(i)(n − 1 − (i mod 2)) + i·δ(i)  ≤  β + i·w(i)(i − 1),
(D2)  w(i)(i − 1) + w(j)(j − 1)  ≤  w(i)(j − 1) + w(j)(i − 1) + δ(i) + δ(j),
```

together with `(T − 1)g ≥ M` and `g(n − 1) ≤ β`, which extend (D1) and (D2) to all degrees
(the proof of `d1_all` and `d2_all`). If the check passes the record is `B`, otherwise V004.

**Why it is a bound.** Summing (D2) over the ordered adjacent pairs `(x, y)` and regrouping
by vertices gives `Σ_x d(x)·w(d(x))(d(x) − 1) ≤ Σ_x w(d(x))·s(x) + Σ_x d(x)·δ(d(x))`;
(L) bounds `s(x)` by `n − 1 − (d(x) mod 2)`; summing (D1) over the vertices and inserting
the handshake `Σ_x d(x) = 2m` gives `2Mm ≤ nβ < 2M(B+1)`, so `m ≤ B`. This is exactly
linear-programming duality for the class LP, with (D2) the dual constraint of an edge
variable and (D1) that of a vertex variable, written so that the offsets `δ` are determined
by the weights and the target.

**Finding the certificates.** For each `n ≤ 1240` a Python script (SciPy 1.18.1 with the
HiGHS solver, exact rational post-processing) solved the class LP restricted to the
certificate's shape (weights zero below `k`, four to six free levels, the linear tail),
took the floor `B` of its optimum, re-solved for the weights of maximal slack at the target
`B`, rounded them to multiples of `1/M`, and verified the rounded certificate with an exact
integer replica of `certOk`. Only the values of `n` at which this beats V004 are stored:
944 of the first 1240 values (735 of the first 1000), by up to 22 edges (`n = 1106`), 7247
edges in all; for example `n = 15: 31 → 30` (the true value), `n = 18: 41 → 40`,
`n = 200: 1458 → 1455`, `n = 1000: 16041 → 16035`. Where the shape with five free levels was
tested against the unrestricted class LP (`n ≤ 130`) it reached the same floor at 99 of
101 values.

**Why a table.** The optimal weights are rational functions of `n` whose form (the set of
tight constraints) changes at more than fifty places below `n = 200`, so no closed formula
was found; the pipeline was designed so that the *only* data needed per `n` are a handful of
integers, and everything else — offsets, target, tail — is computed by the record and
justified by one general theorem. The table is split into lists of one hundred entries to
stay within the elaborator's recursion depth.

## How the proofs were obtained

By the agent, autonomously, after the numerical study. `local_ineq` reuses V003's `mset`
lemmas; `sum_nbr`, `sum_swap`, `sum_fst`, `sum_snd`, `sum_sval` convert between sums over
vertices, over neighbourhoods and over ordered adjacent pairs; `d1_all` and `d2_all` extend
the finitely many checked inequalities to all degrees by the tail formulas (the (D2) case
`i < T < j` follows from the pair `(i, T)` because the difference grows with `j`); `key`
assembles the sums with `omega` on the sums treated as atoms. The whole file elaborates in
23110 heartbeats (heaviest: `d2_all` 4967, `key` 4332, `local_ineq` 4216). Evaluating the
record costs about 1981 heartbeats at `n = 100`, 24372 at `n = 1000` and 36345 at
`n = 1240` (the check is quadratic in the number of listed degrees).

## Sources

- The local inequality (L) is folklore (it is the exact form of Reiman's cherry count at
  one vertex; see also the "missed 2-paths" lemma of Firke–Kosek–Nash–Williford, JCTB 103
  (2013)). No code or data from outside sources was used; the certificates were computed
  for this record.
- OEIS A006855 for the values of `f(n)`, `n ≤ 40`, used only to report gaps.

## Setup

- Tools: Claude Fable 5.1 (`claude-fable-5-1`) running Claude Code, autonomously; one earlier
  consultation of GPT-6 Astra through the `askgpt` tool (literature). Lean 4.31.0 with the
  pinned Mathlib; Python 3.12 with SciPy 1.18.1 (HiGHS) for the certificates.
- Machine: 96 logical cores, 755 GB RAM (32 GB available to this job), Linux 6.8.0-124-generic.
- Time: about 5 hours from the acceptance of V004 to `ACCEPT`, roughly half on the numerical
  study (which certificate shape reproduces the LP) and half on the formalisation.
- Outside Lean: the generator `gen.py` in the scratch directory (LP per `n`, rounding, exact
  verification) ran for about an hour in six chunks; the table in `Def.lean` is its output.
