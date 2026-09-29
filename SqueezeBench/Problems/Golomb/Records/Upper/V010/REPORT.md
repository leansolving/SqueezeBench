# Golomb, upper record, V010

By trial claude-fable.

## How the bound was obtained

**Bound.** `record = min(V009.record, singerLen)` with `singerLen m = (m−1)·q`, `q = primeGe (m−1)`
the least prime `≥ m − 1`. Witness `n₀ = 30`: `898 → 841`. It improves the record at every
`m = q + 1` with `q ≥ 29` prime — infinitely many `m` — where V009 had to use a prime
`p ≥ m + 1`: `(m−1)²` against `⌊(m−1)(p²−1)/p⌋ ≥ (m−1)m`, a saving of at least `m − 1`
(`m = 32`: `1146 → 961`; `m = 102`: `10401 → 10201`). Elsewhere `q` is the least prime `≥ m`
and `(m−1)q` is one more than V009's value, so `min` keeps V009 there.

**Construction.** J. Singer, *A theorem in finite projective geometry and some applications
to number theory*, Trans. AMS 43 (1938), 377–385: for a prime power `q` the points of a line
of `PG(2, q)`, as elements of the cyclic group `GF(q³)ˣ/GF(q)ˣ` of order `q² + q + 1`, form a
perfect difference set with `q + 1` elements, in particular a Sidon set modulo `q² + q + 1`.
Concretely, for a generator `θ` of `GF(q³)ˣ`, the residues `a < q² + q + 1` with
`θᵃ ∈ GF(q) + GF(q)·θ`. V008's window lemma with `n = q² + q + 1`, `k = q + 1` gives
`f m ≤ ⌊(m−1)(q²+q+1)/(q+1)⌋ = (m−1)q` for `m ≤ q + 1`. Only primes `q` are used here, since
Mathlib's `GaloisField p 3` provides `GF(p³)` with `GF(p) = ZMod p` inside it.

## How the proofs were obtained

By an AI agent (see Setup), by hand-written Lean, no search. The algebra is arranged so that
the only facts about `GF(p³)` needed are the order of a generator and three lemmas:

- `mem_base_of_pow_eq_one`: a unit with `x^(p−1) = 1` lies in the prime field, by counting —
  `IsCyclic.card_pow_eq_one_le` bounds the solutions by `p − 1` and `Units.map` of `(ZMod p)ˣ`
  already supplies `p − 1` (`Finset.eq_of_subset_of_card_le`).
- `lin_indep3`: `1, θ, θ²` are independent over `GF(p)`, else all `p³ − 1` distinct powers of
  `θ` lie in `GF(p) + GF(p)θ`, which has at most `p²` elements (`card_le_card_of_injOn`).
- `exp_eq_of_proportional`: `θᵃ = μ θᵇ` with `μ ∈ GF(p)ˣ` and `a, b < p² + p + 1` gives
  `a = b`, by raising to the power `p − 1` and cancelling in `Nat.ModEq`.

The Sidon argument avoids unique factorisation in `GF(p)[T]`: from `θᵃθᵇ = μ θᶜθᵈ` and the
coordinates `θᵉ = xₑ + yₑθ`, comparing the three coefficients gives the identity
`μ·(xₐy_c − yₐx_c)(xₐy_d − yₐx_d) = 0` (a `linear_combination` of the three equations), so
`(xₐ, yₐ)` is proportional to `(x_c, y_c)` or `(x_d, y_d)` (`proportional`), hence `a = c` or
`a = d`; the other exponent follows by cancelling `θᵃ`. The element `0 ∈ D` (the point at
infinity, `θ⁰ = 1`) and the `p` residues `dlog(θ + c) mod (p²+p+1)` give `|D| = p + 1`; the
reduction modulo `p² + p + 1` is legitimate because `θ^(p²+p+1)` has `(p−1)`-th power `1`, so
it is a prime-field scalar.

Iterations: `DecidableEq` for `Finset.image` (`classical`), an `omega` needing `p·p ≥ 4`,
and `Nat.ModEq.mul_right'` (scales the modulus) versus `mul_right`.

## Setup

- Tools: Claude Fable 5.1 (Claude Code CLI) writing all Lean; Lean 4.31.0 with the pinned
  Mathlib. No computation outside Lean.
- Machine: 96 cores (`nproc`), 755 GB RAM reported by `free -g` (32 GB allotted),
  Linux 6.8.0-124-generic.
- Time spent: about 1.5 hours.
