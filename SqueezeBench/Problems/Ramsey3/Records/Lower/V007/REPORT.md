# Ramsey3, lower record, V007

By trial claude-fable.

## The bound

`record = maxWith V006.record v` with `v k = inc (k-1) + 1` for `k ≥ 2` (pinned to `0` below
`nMin = 2`), where `inc m = q³` for the largest prime `q` with `2q² ≤ m` (and `0` if there is
none). So `R(3,k) > q³`, i.e. `R(3,k) = Ω(k^{3/2})`: the exponent rises from `log 6/log 4 ≈ 1.29`
(V005/V006) to `3/2`.

Witness `k = 1683` (`q = 29`): V006 gives `23761`, V007 gives `29³ + 1 = 24390`. The new term
wins on the stretches `k ∈ [1683, 1728]`, `[1923, 2048]`, `[3363, 4096]`, `[4419, 5120]`,
`[5619, 8192]` and at every `k ≥ 8979` (checked by a Python model of both records up to
`k = 200000`; asymptotically `q³ ≈ ((k-1)/2)^{3/2}` against `≈ 2.4 · (k-1)^{1.29}`). Below
`k = 1683` the record is V006's; nothing changes at `k ≤ 100`.

| k | 100 | 1683 | 1923 | 4096 | 10000 | 100000 |
|---|---|---|---|---|---|---|
| V006 | 649 | 23761 | 27217 | 51841 | 134137 | 2099521 |
| V007 | 649 | 24390 | 29792 | 68922 | 148878 | 11089568 |

## How the bound was obtained

The ordered point–line incidence graph, an elementary form of the constructions of
Codenotti–Pudlák–Resta and Kostochka–Pudlák–Rödl, as written up by Kocbek (see *Sources*):
for a prime `p`, a flag is `(x, s, b) ∈ (Z/p)³`, the point `(x, s x + b)` on the non-vertical
line `y = s x + b`; points are ordered by the code `x·p + y ∈ ℕ`; two flags are adjacent when
their lines differ and the smaller point lies on the other's line. It is triangle-free
because two distinct points lie on at most one non-vertical line, and its independence number
is at most `|P| + |L| = 2p²`: split an independent set into the flags whose point is the
largest of the set on their line (at most one per line) and the rest (at most one per point).
`p³` vertices, so `R(3, 2p² + 1) > p³`. The construction was pointed out in a literature
consultation (GPT-6 Astra); both proofs were re-derived by hand before formalising.

Only primes are used (`ZMod p` is a field for prime `p`); prime powers via `GaloisField`
would add `q = 27, 32, 49, 64, 81, 125, 128, …` and make the term win already at `k = 1459`.
The constant is poor by nature (`α ≤ 2p²` on `p³` vertices, ratio `p/2`), which is why V006's
`35/8 · 1.5^r` chain stays ahead until `k ≈ 1700`.

## How the proofs were obtained

By hand (the model below), in V005's `Good` framework.

- `two_points`: `(s - s')(x - x') = 0` by `linear_combination`, then `mul_eq_zero`.
- `no_triangle`, `ig_cliqueFree`: the relation orders the point codes, so of the eight
  orientations of a triangle two are cyclic (`omega`) and six reduce to `f < g < h`.
- `ig_indep_card_le`: `card_filter_add_card_filter_not` and two `card_le_card_of_injOn` into
  `univ : Finset (ZMod p × ZMod p)` of cardinality `p * p` (`Fintype.card_prod`, `ZMod.card`).
  `ptc_inj` (the code determines the point) is two `nlinarith` calls from `ZMod.val_lt`.
- `good_inc`: `Fintype.equivFinOfCardEq` from `(Z/p)³` to `Fin (p * (p * p))`, then V005's
  `goodOn_comap`.
- The record function: `isPrime` (trial division), `isqrt` (linear search with fuel),
  `primeBelow` (downward search with fuel), all structurally recursive so that `decide +kernel`
  evaluates them; `inc_spec` packages `isqrt_le`, `primeBelowAux_le`, `primeBelowAux_prime`,
  `isPrime_prime` (`Nat.prime_def_lt`). `strict` is `decide +kernel` at `k = 1683`
  (`V006.g 1682` unfolds five times; `isqrt 841 = 29` in 30 steps; `isPrime 29` in 29).

Nothing was abandoned. `ptc_inj` is the largest declaration (about 20k heartbeats); the file
is far below the budget (see `squeeze verify`).

## Sources

- M. Kocbek, *Explicit geometric construction of Ramsey graphs*, arXiv:2507.09235 (2025),
  Definition 2.2, Theorems 2.3 and 2.4 (the ordered incidence graph and the bound
  `α ≤ |A| + |B|`); the affine-plane instance is the case `m = 2`, `λ = 1` of §3.
- B. Codenotti, P. Pudlák, G. Resta, *Some structural properties of low-rank matrices related
  to computational complexity*, Theoret. Comput. Sci. 235 (2000) 89–107; A. Kostochka,
  P. Pudlák, V. Rödl, *Some constructive bounds on Ramsey numbers*, J. Combin. Theory Ser. B
  100 (2010) 439–445 — the origin of the construction and of its combinatorial independence
  proof.
- Mathematical constructions only; no outside code or data files were used. All Lean code
  was written in this session, adapting only the earlier versions listed in `based-on`.

## Setup

- Tools: Claude Fable 5.1 (`claude-fable-5-1`) running Claude Code, with GPT-6 Astra
  (`askgpt` MCP tool) consulted once for the literature (the same consultation as for V005).
  Lean 4.31.0 with the project's pinned Mathlib. Python 3 (no packages) to locate the
  crossover with V006.
- Machine: Linux 6.8.0-124-generic, 96 logical CPUs, 755 GB RAM (32 GB available to this
  session).
- Time: about one hour after V006. No computation outside Lean besides the crossover scan.
