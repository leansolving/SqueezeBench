# Golomb, upper record, V009

By trial claude-fable.

## How the bound was obtained

**Bound.** `record = min(V008.record, bcLen)` with `bcLen m = ⌊(m−1)(p²−1)/p⌋`, `p = primeGe m`
the least prime `≥ m`. Witness `n₀ = 31`: `1110 → 929`. It improves the record at every
`m ≥ 29`: by about `3m` at prime `m` (`m = 29`: `868 → 811`; `m = 101`: `10300 → 10099`),
where V008 had to use the *next* prime, and by exactly one elsewhere (`m = 30`: `899 → 898`),
since `⌊(m−1)(p²−1)/p⌋ = (m−1)p − 1` for `1 ≤ m − 1 < p`.

**Construction.** R. C. Bose and S. Chowla, *Theorems in the additive theory of numbers*,
Comment. Math. Helv. 37 (1962/63), 141–147 (the `q` residues modulo `q² − 1` are Bose's
1942 construction). For a generator `θ` of `GF(p²)ˣ`, the `p` discrete logarithms `a` with
`θᵃ ∈ θ + GF(p)` form a Sidon set modulo `p² − 1`: if `a + b ≡ c + d` then
`(θ + x)(θ + y) = (θ + z)(θ + w)` in `GF(p²)`, and since `1, θ` are independent over `GF(p)`
the coefficients give `x + y = z + w`, `xy = zw`, hence `{x, y} = {z, w}`. V008's window
lemma `f_le_of_sidonMod` (`k` residues Sidon modulo `n` give `f m ≤ ⌊(m−1)n/k⌋`) turns
this into the bound, with `n = p² − 1`, `k = p`.

## How the proofs were obtained

By an AI agent (see Setup), by hand-written Lean, no search; compiled first time.

- `GaloisField p 2` from Mathlib: `Field`, `Finite`, `Algebra (ZMod p)`, cyclic units
  (`instIsCyclicUnitsOfFinite`), `GaloisField.card` and `Nat.card_units` give
  `orderOf θ = p² − 1` for the generator from `IsCyclic.exists_monoid_generator`.
- `gen_not_base`: `θ = c ∈ GF(p)` would give `θ^(p−1) = 1` (`ZMod.pow_card_sub_one_eq_one`),
  so `p² − 1 ≤ p − 1`. `lin_indep`: if `x + yθ = x' + y'θ` with `y ≠ y'` then `θ ∈ GF(p)`.
- Discrete logarithms via `Submonoid.mem_powers_iff` and `pow_mod_orderOf`, chosen with
  `choose`; the set is `univ.image`, its cardinality `p` by injectivity (`ZMod.card`).
- `f_le_bose_chowla`: the Sidon-mod-`(p² − 1)` argument, `pow_eq_pow_iff_modEq`, and the two
  arithmetic side conditions of the window lemma (`Nat.div_lt_of_lt_mul`,
  `Nat.lt_mul_div_succ`).
- `primeGe` and `primeGe_spec` are V002's `nextPrime` and `nextPrime_spec` with `≥` in
  place of `>`, so that a prime `m` may serve as its own `p`.

## Setup

- Tools: Claude Fable 5.1 (Claude Code CLI) writing all Lean; Lean 4.31.0 with the pinned
  Mathlib. No computation outside Lean.
- Machine: 96 cores (`nproc`), 755 GB RAM reported by `free -g` (32 GB allotted),
  Linux 6.8.0-124-generic.
- Time spent: about 40 minutes.
