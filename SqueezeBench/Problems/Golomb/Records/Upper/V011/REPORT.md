# Golomb, upper record, V011

By trial claude-fable.

## How the bound was obtained

**Bound.** `record = min(V010.record, singerPPLen)` with `singerPPLen m = (m−1)·q`,
`q = primePowGe (m−1)` the least prime *power* `≥ m − 1`. Witness `n₀ = 33`: `1183 → 1024`.
It improves the record exactly where the least prime power `≥ m − 1` is not a prime and is
smaller than the least prime: up to `m = 140` that is `m = 33` (`q = 32`), `49, 50` (`49`),
`63–65` (`64`), `81, 82` (`81`), `115–122` (`121`), `123–126` (`125`), `129` (`128`); there are
infinitely many such `m`, one block for every prime power `pᵏ`, `k ≥ 2`, that is followed by a
prime gap.

**Construction.** Singer's theorem (V010) holds for every finite field `GF(q)`, `q = pᵏ`:
`q + 1` residues Sidon modulo `q² + q + 1`, hence `f m ≤ (m−1)q` for `m ≤ q + 1` through V008's
window lemma. V010 restricted to primes because it worked inside `GaloisField p 3` with the
prime field `ZMod p`. Here `GF(q) = GaloisField p k` and `GF(q³) = GaloisField p (3k)`, with
an embedding from Mathlib's `FiniteField.nonempty_algHom_of_finrank_dvd` (`k ∣ 3k`).

## How the proofs were obtained

By an AI agent (see Setup), by hand-written Lean, no search in Lean.

The proof is V010's, restated over an arbitrary finite field `K` with `Nat.card K = q` and a
ring homomorphism `ι : K →+* L` into a field with `Nat.card L = q³`. Auditing V010 for what it
used about `ZMod p` gave three things: `|GF(p)| = p`, `x^(p−1) = 1` for `x ≠ 0`, and the
injectivity of the embedding. The second is Lagrange in `Kˣ` (`pow_card_eq_one'` with
`Nat.card_units`), the third holds for any ring homomorphism out of a field. Everything else —
`mem_base_of_pow_eq_one` (units with `x^(q−1) = 1` are `ι(Kˣ)`, by counting in the cyclic group
`Lˣ`), `lin_indep3`, `exp_eq_of_proportional`, `proportional`, the Singer set and its Sidon
property — went through unchanged apart from names, with `Fintype.ofFinite` and
`Fintype.card_eq_nat_card` where `Finset.univ` is needed. `f_le_singer_pp` instantiates with
`GaloisField.card` and `GaloisField.finrank`, and `primePowGe_spec` is V009's `primeGe_spec`
with Bertrand's prime read as a prime power.

The record's search uses Mathlib's `Decidable (IsPrimePow n)` instance
(`isPrimePow_nat_iff_bounded_log_minFac`), which the kernel evaluates quickly enough:
`primePowGe 120 = 121` settles by `decide +kernel` at once. Compiled first time; the only
fixes were `omit [Finite _] in` for the linter.

## Setup

- Tools: Claude Fable 5.1 (Claude Code CLI) writing all Lean; Lean 4.31.0 with the pinned
  Mathlib. `#eval` in a scratch file to list the `m ≤ 140` at which the bound improves.
- Machine: 96 cores (`nproc`), 755 GB RAM reported by `free -g` (32 GB allotted),
  Linux 6.8.0-124-generic.
- Time spent: about 40 minutes.
