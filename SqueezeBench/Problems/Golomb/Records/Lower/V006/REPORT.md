# Golomb, lower record, V006

By trial claude-opus-5.5.

## How the bound was obtained

**Bound.** With `M = t m − t(t+1)/2` (the number of differences of order at most `t`),
`G j = g 1 + … + g j` for a valid lower bound `g`, and `t ∈ {⌊√m⌋ − 1, ⌊√m⌋}`,

```
lind g m t = ⌈ (M (M + 1) + 4 ∑_{j=1}^{t} G j) / (t (t + 1)) ⌉        (0 < t < m)
record m   = max (V005.record m) (lind (record at smaller arguments) m t)
```

computed with structural fuel (`core`), so the boundary terms use the record itself.

**Idea.** Lindström's argument for B₂-sequences, with a boundary correction. Sort the marks
`a₀ < … < a_{m−1}` of a ruler of length `L`. The `M` differences `a_{i+j} − a_i` with
`1 ≤ j ≤ t` are distinct (Sidon property) positive integers, so their sum is at least
`M(M+1)/2`. The order-`j` differences telescope to `∑_{r<j} (a_{m−j+r} − a_r)`; the first
`r + 1` marks form a ruler of length at most `a_r`, so `a_r ≥ f(r+1) ≥ g(r+1)`, and the last
`r + 1` marks likewise give `L − a_{m−1−r} ≥ g(r+1)` after the reflection `x ↦ L − x`.
Hence the order-`j` sum is at most `jL − 2 G j`, and summing over `j ≤ t`

```
M (M + 1) + 4 ∑_{j ≤ t} G j ≤ t (t + 1) L .
```

This is a different argument from the Erdős–Turán sliding window of V001–V005 (same
leading terms `m² − 2m^{3/2}`), and with the boundary correction it is better by `Θ(m)`:
the correction uses `f(r+1) ≳ r²` for every prefix, where V003–V005 only had the pair
count `C(k, 2) ≤ s` on a few blocks.

**Numbers.** Improves V005 at 394 of the 400 values `1 ≤ m ≤ 400` (all but
`m = 1, 2, 3, 4, 5, 8`), e.g. `m = 6: 15 → 16`, `27: 488 → 489`, `100: 8143 → 8148`,
`200: 34624 → 34639`, `400: 144558 → 144591`. The gain grows linearly in `m`, so it holds at
infinitely many `n`. The optimal order is always `⌊√m⌋` or `⌊√m⌋ − 1` over
`1 ≤ m ≤ 1000` (checked numerically against all `1 ≤ t < m`), so only those two are tried.

**Witness.** `n₀ = 100`: `8143 → 8148`.

## How the proofs were obtained

By hand, written by the agent, in one pass with two small fixes. The sorted marks come from
`Finset.orderEmbOfFin`; `card_mul_le_sum` (distinct positive integers) is an induction with
`Finset.induction_on_max`; the differences are indexed by
`idx m t = {(j, i) : j < t, i + j + 1 < m}` and their injectivity is the Sidon property;
`telescope` is two applications of `Finset.sum_range_add`; `prefix_le` and `suffix_le`
exhibit the sub-ruler (reflected for the suffix) as a member of `RulerLengths`. Validity of
the bootstrapped record is an induction on the fuel. `strict` is `decide +kernel` at 100.

Cost: 23019 heartbeats in all; heaviest `master` 3659.

## Sources

No code from outside sources. Mathematics: B. Lindström, *An inequality for B₂-sequences*,
J. Combin. Theory 6 (1969) 211–212 (the sum-of-differences argument). V005's record and
validity are used as the base of the bootstrap, and V001's `isqrt`.

## Setup

- Tools: Claude Opus 5.5 (`claude-opus-5-5`) as the agent in Claude Code; one consultation
  of GPT-6 Astra for literature; Python for numerical comparisons of candidate bounds.
- Machine: 96 cores (`nproc`), 755 GB RAM (`free -g`; the session is capped at 32 GB),
  Linux 6.8.0-124-generic.
- Time: about one hour. No computation outside Lean enters the proof.
