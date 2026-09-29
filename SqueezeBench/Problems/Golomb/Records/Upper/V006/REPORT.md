# Golomb, upper record, V006

By trial claude-fable.

## How the bound was obtained

**Bound.** `record = min(V005.record, ruzsaLen)` with `ruzsaLen m = p(p−1) − 1`, where
`p = nextPrime m` is V002's least prime above `m`. Since `p ≈ m` this is `≈ m²`, against the
`≈ 2m²` of the Erdős–Turán ruler that V002 contributed. Witness `n₀ = 18`: `650 → 341`.

**Construction.** I. Z. Ruzsa, *Solving a linear equation in a set of integers I*, Acta
Arith. 65 (1993), 259–282, §4: for a prime `p` and a primitive root `g` modulo `p`, the
`p − 1` residues `x ≡ i (mod p−1)`, `x ≡ gⁱ (mod p)` (`1 ≤ i ≤ p − 1`) form a Sidon set
modulo `p(p−1)`. Representatives in `[0, p(p−1))` are then a Golomb ruler with `p − 1` marks
and largest mark at most `p(p−1) − 1`, and any `m ≤ p − 1` of them still form a ruler, so
`f(m) ≤ p(p−1) − 1` for every prime `p > m`.

The construction needs no field extension — only `ZMod p` and a generator of `(ZMod p)ˣ`,
which Mathlib supplies (`IsCyclic.exists_generator`, `ZMod.card_units`). That is why it was
chosen over Bose–Chowla (`f(q) ≤ q² − 2`, needs `GF(q²)`) and Singer (`f(q+1) ≤ q² + q`,
needs `GF(q³)`): it halves the record at every `m ≥ 18` for a proof of about 150 lines.
Bose–Chowla would still beat it at prime `m`, and Singer at `m = prime + 1`.

## How the proofs were obtained

By an AI agent (see Setup), by hand-written Lean, no search.

- The mark of index `i` is `(p·i + (p−1)·val(gⁱ)) mod p(p−1)`: it is `≡ i (mod p−1)` since
  `p ≡ 1`, and `≡ −gⁱ (mod p)`. (The sign is harmless: `−g` is as good as `g`.)
- `ruzsaRuler_sidon`: from `aᵢ + aⱼ = aₖ + aₗ` in `ℕ`, reduce modulo `p − 1` to get
  `i + j ≡ k + l`, hence `gⁱgʲ = gᵏgˡ` in `(ZMod p)ˣ` (`pow_eq_pow_iff_modEq`, order `p − 1`);
  reduce modulo `p` to get `gⁱ + gʲ = gᵏ + gˡ`; then `(gⁱ − gᵏ)(gⁱ − gˡ) = 0` in the field
  `ZMod p`, and `pow_injOn_Iio_orderOf` turns equal powers into equal indices.
- `f_le_of_sidon`: a Sidon set with `≥ m` elements below `N` gives `f m ≤ N − 1`, by taking
  an `m`-element subset (`Finset.exists_subset_card_eq`) and its maximum as the length.
- Everything else is bookkeeping: `nextPrime_spec` from V002 supplies the prime, the
  witness comparison is `decide +kernel`.

Nothing was hard; the only iteration was a `rw` motive error in the modular identity
`p·i + (p−1)·v = (p−1)(i+v) + i`, fixed by stating it as a separate lemma on naturals.

## Setup

- Tools: Claude Fable 5.1 (Claude Code CLI) writing all Lean; Lean 4.31.0 with the pinned
  Mathlib. No external search, no computation outside Lean.
- Machine: 96 cores (`nproc`), 755 GB RAM reported by `free -g` (32 GB allotted),
  Linux 6.8.0-124-generic.
- Time spent: about one hour, including reading the previous records.
