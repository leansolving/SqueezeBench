# ExC4, upper record, V004

By trial claude-fable.

## How the bound was obtained

The bound is a *restricted cherry count* around a vertex `x` of maximum degree `d`, the first
step of Füredi's proof that the polarity graphs are extremal at `n = q² + q + 1` for even `q`
(Z. Füredi, *Graphs without quadrilaterals*, JCTB 34 (1983), 187–190). Let `S` be the set of
vertices that are not neighbours of `x` (`x` itself included, so `|S| = n − d`) and, for every
vertex `v`, let `a_v` be the number of neighbours of `v` in `S`. Two distinct vertices of `S`
have at most one common neighbour, so the ordered pairs of distinct neighbours of `v` inside
`S`, over all `v`, are pairwise disjoint and

```
Σ_v a_v (a_v − 1)  ≤  (n − d)(n − d − 1).
```

Every vertex `v ≠ x` has at most one neighbour inside `N(x)` (two would be two common
neighbours of `v` and `x`), so `a_v ≥ d(v) − 1`. The chord of the convex function `a(a − 1)`
between the integers `p` and `p + 1` is the inequality `2pa ≤ a(a − 1) + p(p + 1)`, valid for
every integer `a` (it is `(a − p)² ≥ a − p`). Summing it over the `n − 1` vertices `v ≠ x` and
inserting the handshake `Σ_{v ≠ x} d(v) = 2m − d` gives

```
4pm  ≤  2pd + (n − 1)p(p + 3) + (n − d)(n − d − 1),
```

for every `p ≥ 1`, which is `bp n d p` in `Def.lean`. Since `d` is the maximum degree,
`2m ≤ nd` as well. The record is the largest, over `d < n`, of
`min(⌊nd/2⌋, bp n d p)`, folded into V003 by `minWith`. The chord level is
`p = ⌊2·V003(n)/n⌋ − 1`, one below the average degree V003 still allows; a Python check
showed that this single choice loses nothing against the best `p` at every `n ≤ 600`.

Why it helps: the restricted count deletes the `d` neighbours of `x` from the cherry count, and
what it costs in the count (`n(n−1)` becomes `(n−d)(n−d−1)`) is more than what the degree sum
loses (`2m` becomes `2m − d`) as soon as the maximum degree exceeds the average degree by a
fraction of an edge. The candidate `⌊nd/2⌋` is increasing in `d` and `bp` is decreasing, so the
scan finds the crossover, which sits at `d = ⌈2m/n⌉` and is where an integral maximum degree
is forced above the real average. The record improves V003 at 1467 of the first 2000 values of
`n` (by up to 12 edges, at `n = 1000`), for example `n = 27: 75 → 74`, `n = 100: 521 → 520`,
`n = 1000: 16053 → 16041`.

The choice of this bound came out of a numerical study: a linear program over degree classes
with the per-vertex constraint `Σ_{y ∈ N(x)} (d(y) − 1) ≤ n − 1 − (d(x) mod 2)` beats V003 at
about 70% of the values `n ≤ 400`, and a consultation with GPT (via the `askgpt` tool) pointed
to Füredi's 1983 restricted count, which turned out to be as strong as that LP at many `n`, to
beat it at some, and to have a proof of the same shape as V001 and V003.

## How the proofs were obtained

By the agent, autonomously, in one pass. `sum_aset_le` is the disjoint-union argument of
V003's `sum_sq_le` restricted to `S`; `degree_le_aset` is `Finset.card_le_one` on
`N(v) ∩ N(x)`; `chord` is proved by the two substitutions `p = a + c` and `a = p + 1 + c`
followed by `nlinarith`, as in V003's `tangent`; `key` assembles the sums with `omega` on the
products treated as atoms; `v_valid` picks a vertex of maximum degree with
`Finset.exists_max_image` and reads the scan through `cand_le_scanMax`. The whole file elaborates
in 15713 heartbeats (heaviest: `chord` 4059, `key` 3309, `v_valid` 2459).

The record is cheap for the kernel: evaluating it at `n = 100` takes about 440 heartbeats and at
`n = 1000` about 22000, the scan over `d` being `n` evaluations of a fixed polynomial expression.

## Sources

- Z. Füredi, *Graphs without quadrilaterals*, J. Combin. Theory Ser. B 34 (1983), 187–190:
  the restricted cherry count (mathematical idea only; no code or data taken).
- OEIS A006855 (values of `f(n)` for `n ≤ 40`, used only to report the gaps in this file).

No code from outside sources was used. The LP experiments used SciPy 1.18.1 (HiGHS) in a
Python 3.12 virtual environment; they are not part of the record.

## Setup

- Tools: Claude Fable 5.1 (`claude-fable-5-1`) running Claude Code, autonomously; one
  consultation of GPT-6 Astra through the `askgpt` tool (literature survey and the pointer to
  Füredi 1983). Lean 4.31.0 with the pinned Mathlib.
- Machine: 96 logical cores, 755 GB RAM (32 GB available to this job), Linux 6.8.0-124-generic.
- Time: about 3 hours from the start of the session to `ACCEPT`, most of it on the numerical
  study of candidate bounds; the Lean proof took under an hour.
- Outside Lean: Python replicas of the record functions (`records.py`, `v004.py` in the scratch
  directory) to count improvements and choose the witness and the chord level; the degree-class
  linear programs described above.
