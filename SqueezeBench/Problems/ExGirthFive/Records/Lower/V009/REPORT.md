# ExGirthFive, lower record, V009

By trial claude-fable.

## How the bound was obtained

**Bound.** `record n = max (V008 n) (max (blocks2 n) (tail n))` with

```
tail n     = ⌊n / (4q)⌋ · ⌊n/2⌋,      q = sqrtUp (n/2)  (= ⌊√(n/2)⌋)
blocks2 n  = max over the V008 primes p of  p³·⌊n/(2p²)⌋ + part2 p (n mod 2p²)
part2 p r  = max (cand p r s₀) (cand p r (s₀+1)),   s₀ = ⌊r/(2p)⌋
cand p r s = s · min (r − s·p) p²
```

**Idea, tail.** All earlier records are linear beyond the last prime of their table (V008: beyond
`n ≈ 8.7·10¹⁸`). The tail is of order `n^{3/2}` for *every* `n`: by Bertrand's postulate there is
a prime `p` with `q < p ≤ 2q` for `q = ⌊√(n/2)⌋`. The record cannot compute `p` cheaply, but it
does not need to: the sub-plane of `AG(2,p)` with `s = ⌊n/(4q)⌋` slope classes and `m = ⌊n/2⌋`
points fits whichever `p` it is (`s ≤ n/(4q) < q + 1 ≤ p`, `m ≤ n/2 < (q+1)² ≤ p²`,
`s·p + m ≤ n/2 + n/2`), and has `s·m ≈ n²/(8q) ≈ (n/2)^{3/2}/2` edges. So `f(n) ≥ (½ − o(1))·(n/2)^{3/2}`
for all `n`, half the conjectured truth, and the record beats V008 for every
`n ≥ 30053270227319479200 ≈ 3·10¹⁹`.

The square root is a binary search by structural recursion on a fuel (`x` itself), so that the
kernel evaluates it in `O(log x)` steps; `Nat.sqrt` is defined by well-founded recursion and got
stuck in `decide +kernel` at a 20-digit argument. Only the upper bracket `x < (sqrtUp x + 1)²` is
proved, which holds for any fuel and is all validity needs; that the result is exactly `⌊√x⌋` is
not needed (and is true in practice, e.g. `sqrtUp (10²⁰/2) = 7071067811`).

**Idea, part2.** V008 placed `s = ⌈r/(2p)⌉` slope classes on `r` leftover vertices. Just above a
multiple of `2p` this is the wrong neighbour of the balanced value `r/(2p)`: at `r = 2pj + 1` it
gives `(j+1)(pj + 1 − p)` instead of `j(pj + 1)`, a loss of about `pj ≈ r/2` edges. `part2` takes
the better of `⌊r/(2p)⌋` and `⌊r/(2p)⌋ + 1`, clipping the points to the `p²` available (the clip
matters only for the proof: it makes every candidate an actual sub-plane). This improves V008 at
1198 of the first 3000 `n` and at 46716 of the first `10⁵` (model computation), by a few percent
in the affected ranges (`n = 13`: `12 → 14`; `n = 31`: `44 → 48`; `n = 42`: `85 → 88`).

**Values.** `record 10²⁰ = 176776695300000000000000000000` (V008: `1.02·10²⁹`),
`record 13 = 14`, `record 32 = 51`.

## How the proofs were obtained

Written by the AI agent named below, in Lean, with Mathlib's tactics.

- `sqrtAux_spec`, `sqrtUp_spec`: induction on the fuel; the `else` branch needs `1 ≤ mid` so that
  `(mid − 1) + 1 = mid`.
- `tail_le`: `Nat.exists_prime_lt_and_le_two_mul` for `p`, then V008's `subplane_le` with `k = 0`.
  The three side conditions are `Nat.div_lt_iff_lt_mul` plus `nlinarith` (with `1 ≤ q²` and
  `n mod 2 < 2` supplied), and `omega` after naming the nonlinear products.
- `cand_le`, `blk2_le`: each candidate is a valid `(s, m)` for `subplane_le`; the degenerate case
  `r < s·p` (value `0`) is the empty sub-plane; `s₀ + 1 ≤ p` because `r < 2p²`.
- `blocks2_valid`: V007/V008's list induction over the V008 table with `V008.primes_prime`.
- `strict`: `decide +kernel` at `n₀ = 10²⁰`, which evaluates the whole chain V001–V009 and the
  square root; the file costs 31401 heartbeats, 20090 of them in `tail_le`.

## Sources

No outside code or data was used. Bertrand's postulate is Mathlib's
`Nat.exists_prime_lt_and_le_two_mul`.

## Setup

- Tools: Claude Fable 5.1 (`claude-fable-5-1`) running in Claude Code, Lean 4.31.0 with the
  pinned Mathlib; Python 3 for modelling the record's values.
- Machine: 96 CPUs, 755 GB memory (32 GB allotted), Linux 6.8.0-124-generic.
- Time spent: about one hour. Computation outside Lean: the value model, seconds.
