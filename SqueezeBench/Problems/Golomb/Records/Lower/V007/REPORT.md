# Golomb, lower record, V007

By trial claude-opus-5.5.

## How the bound was obtained

**Bound.** Call a set of `k` index intervals of `n` consecutive marks each *separated* if any
two share at most one mark. `H fuel k n` bounds the total span of such a family:

```
H 0 k n      = k · V006.record n
H (f+1) k n  = max (k · V006.record n) (max over u ∈ {⌊√n⌋−2, …, ⌊√n⌋+1} of lindK)
lindK k n u  = ⌈ (Q (Q + 1) + 2 ∑_{o=1}^{u} ∑_{r=1}^{o−1} H f (2k) (r+1)) / (u (u + 1)) ⌉,
               Q = k (u n − u(u+1)/2),   when 0 < u < n and 2u ≤ n + 1
record m     = H m 1 m
```

**Idea.** V006 bounded the boundary terms of Lindström's sum, `b_r = a_r + (L − a_{m−1−r})`
(first plus last `r + 1` marks), by `2 f(r+1)`. But the first and the last `r + 1` marks share
no pair, so *all* their differences are distinct together, and Lindström's argument applied to
the two pieces jointly gives `b_r ≳ 4r²` instead of `2r²`. The same applies recursively: the
`2k` end pieces of a separated family of `k` intervals form a separated family again
(`2r ≤ n − 1`), so one inequality, applied at every level, handles the whole recursion. For
`k` intervals the order-`≤ u` differences number `Q`, are distinct, and telescope to
`u(u+1)/2 · (total span) − ∑_{o ≤ u} ∑_{1 ≤ r < o} b_r`.

The observation that the two end sub-rulers have disjoint difference sets came from a
consultation of GPT-6 Astra (answering a question about refinements of Lindström's bound);
the recursive family version, the choice of parameters and the proofs are ours.

**Numbers.** Improves V006 at 394 of the 400 values `1 ≤ m ≤ 400` (all but
`1, 2, 3, 4, 6, 7`), e.g. `m = 5: 10 → 11` (exact), `27: 489 → 493`, `50: 1867 → 1875`,
`100: 8148 → 8165`, `200: 34639 → 34676`, `400: 144591 → 144671`; the gain grows linearly.
The four orders `u` and the fuel are enough: over `1 ≤ m ≤ 400` the value equals the
maximum over all `u` with deeper fuel (checked numerically).

**Witness.** `n₀ = 100`: `8148 → 8165`.

## How the proofs were obtained

By hand, written by the agent; two trivial fixes after the first build. `Sep m w Ls` states
that the start indices `Ls` give intervals `[l, l + w]` inside `[0, m)` with `l + w ≤ l'`
for `l < l'`. `family_master` indexes the differences by `Ls ×ˢ idx (w+1) u` (V006's `idx`),
proves injectivity from the Sidon property and the separation, and applies V006's
`card_mul_le_sum`; `order_eq` is V006's `telescope` for the shifted sequence, rearranged into
span and end pieces; `split_sep` shows that the end pieces form a separated family of `2k`
intervals with the right total span; `H_le` is the induction on the fuel; the base case
translates each interval to a ruler (`interval_le`, `isSidon_shift`).

Cost: 30224 heartbeats in all; heaviest `family_master` 8415.

## Sources

No code from outside sources. Mathematics: B. Lindström, *An inequality for B₂-sequences*,
J. Combin. Theory 6 (1969) 211–212; the two-end observation as described above. V006's
record, validity and lemmas, and V001's `isqrt`, are reused.

## Setup

- Tools: Claude Opus 5.5 (`claude-opus-5-5`) as the agent in Claude Code; GPT-6 Astra for
  one literature consultation; Python (with SciPy/HiGHS for an LP relaxation used only for
  exploration) for numerical comparisons.
- Machine: 96 cores (`nproc`), 755 GB RAM (`free -g`; the session is capped at 32 GB),
  Linux 6.8.0-124-generic.
- Time: about one and a half hours. No computation outside Lean enters the proof.
