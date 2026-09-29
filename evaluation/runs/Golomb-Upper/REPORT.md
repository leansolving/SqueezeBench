# Golomb — upper track — report

Submitters: `baseline claude-opus-5` (V001–V005), then `trial claude-fable` (V006 on).

`f(m)` is the least length of an `m`-mark Golomb ruler (Sidon set), OEIS A003022.

## Literature

- **Exact values.** A003022 gives `f(2..12) = 1, 3, 6, 11, 17, 25, 34, 44, 55, 72, 85`, and
  exact values are known up to `m = 28` (`f(27) = 553`, `f(28) = 585`, distributed.net
  OGR-27/OGR-28). These come from exhaustive search and are reporting-only here
  (`docs/DESIGN.md` §2.2).
- **Singer (1938), *A theorem in finite projective geometry…*.** A perfect difference set
  modulo `q² + q + 1` for a prime power `q` gives `f(q + 1) ≤ q² + q`. Only defined when
  `q` is a prime power, so it is not a total bound; it is the best known asymptotic shape,
  `f(m) ≈ m²`.
- **Bose–Chowla (1962).** A Sidon set of `q` elements in `ℤ/(q² − 1)` for a prime power `q`,
  giving `f(q) ≤ q² − 2`. Again only for prime powers.
- **Erdős–Turán (1941), *On a problem of Sidon in additive number theory…*.** For a prime
  `p`, `{2pk + (k² mod p) : k < p}` is a Sidon set. Truncating it to its first `m ≤ p`
  marks gives `f(m) ≤ 2p(m − 1) + ((m − 1)² mod p)`, which is elementary and **total** once
  a prime `p ≥ m` is supplied. This is the route taken here.
- **Prime gaps.** Bertrand's postulate (`Nat.exists_prime_lt_and_le_two_mul` in Mathlib)
  gives a prime in `(m, 2m]`, hence the closed form `f(m) ≤ 4m² − 2m − 1` for all `m ≥ 2`.
  Sharper gap results (Baker–Harman–Pintz, `p_{k+1} − p_k ≪ p^{0.525}`) would give
  `f(m) ≤ (2 + o(1))m²`, but are not in Mathlib.

- **Ruzsa (1993), *Solving a linear equation in a set of integers I*, Acta Arith. 65,
  259–282, §4.** For a prime `p` and a primitive root `g` mod `p`, the `p − 1` residues
  `x ≡ i (mod p−1)`, `x ≡ gⁱ (mod p)` form a Sidon set modulo `p(p−1)`. Representatives in
  `[0, p(p−1))` give `f(m) ≤ p(p−1) − 1` for every prime `p > m`. Needs only `ZMod p` and
  a generator of `(ZMod p)ˣ` — no field extension — and is `(1 + o(1))m²`; this is V006.
- **Known optimal rulers.** OEIS A003022 lists `f(m)` through `m = 28`, and Wikipedia's
  *Golomb ruler* table (from Shearer's, Dollas–Rankin–McCracken's and distributed.net's
  searches) gives an optimal ruler at each of these `m`; each ruler is a certificate for
  `f(m) ≤ length` that the kernel can check.
- **Best known rulers beyond `m = 28`.** J. B. Shearer's table of shortest known rulers
  (IBM, to 150 marks, from the affine/projective constructions) and T. Rokicki and G. Dogon,
  *Larger Golomb rulers* (Gathering 4 Gardner 12, 2016; data at `cube20.org/golomb` for
  `m ≤ 40000`: `golomb-all-*` has marks, length, construction `pp`/`ap`, `q`, multiplier;
  `rulers-all-*.zip` the rulers). Each is the best window of `m` consecutive residues of a
  Singer (`q + 1` residues mod `q² + q + 1`) or Bose (`q` residues mod `q² − 1`) modular ruler
  over all multipliers coprime to the modulus and all rotations. No ruler with more than 16
  marks shorter than these constructions give is known. V012–V013 tabulate `m = 29, …, 100`.
- **Window (truncation) lemma.** A Sidon set modulo `n` with `k` residues contains `m`
  residues in a cyclic window of length `⌊(m−1)n/k⌋` (double counting), giving
  `f(m) ≤ ⌊(m−1)n/k⌋`: `(m−1)p` for Ruzsa, `⌊(m−1)(p²−1)/p⌋` for Bose–Chowla, `(m−1)q` for
  Singer. This is V008's `f_le_of_sidonMod`, the general lemma V009–V011 plug into.

Asymptotically the truth is `f(m) = (1 + o(1))m²`. Ruzsa, Bose–Chowla and Singer all reach
`(1 + o(1))m²` along primes; they differ by lower-order terms and at which `m` they apply:
for `p` prime, Ruzsa gives `p − 1` marks in `p² − p − 1`, Bose–Chowla `p` marks in `p² − 2`,
Singer `p + 1` marks in `p² + p`.

## Starting record (V000, the seed)

`min(2^(m−1) − 1, 2m³ − m² − 2m + 1)`, patched to `11` at `m = 5` and `17` at `m = 6`:
the binary ruler `{0, 1, 3, 7, …}` and the cubic ruler `aᵢ = 2m²i + i²`. Exponential up to
`m ≈ 13`, cubic after that.

## V001 — `baseline claude-opus-5`

**Bound.** `record = min(V000.record, 4m² − 2m − 1)`. Witness `n₀ = 10`: `511 → 379`.

**Idea.** Erdős–Turán modulo a prime `p`, truncated to `m` marks: `aₖ = 2pk + (k² mod p)`
for `k < m ≤ p`. Residues are `< p`, so `aᵢ + aⱼ` determines `i + j` (as the quotient by
`2p`) and `(i² mod p) + (j² mod p)` (the remainder, `< 2p`); reducing in the field
`ZMod p` with `p` odd gives `i + j = k + l` and `i² + j² = k² + l²`, hence `ij = kl` and
`(i − k)(i − l) = 0`, so `{i, j} = {k, l}`. The ruler's length is
`2p(m − 1) + ((m − 1)² mod p)`; Bertrand's postulate supplies `m < p ≤ 2m`, so the length
is at most `2·2m·(m − 1) + (2m − 1) = 4m² − 2m − 1`.

**Why.** It is quadratic where the previous record was exponential (small `m`) or cubic
(large `m`), so it improves the record at **every** `m ≥ 10` — infinitely many `n` — and it
is the improvement the problem README pointed at. Natural subtraction makes the closed form
`0` at `m = 0` and `1` at `m = 1`, both still valid, so no padding is needed.

`div_unique` is reused from V000 (`based-on = ["V000"]`). Cost: 24835 heartbeats of the
200000 budget.

## V002 — `baseline claude-opus-5`

**Bound.** `record = min(V001.record, 2p(m−1) + ((m−1)² mod p))` with `p = nextPrime m`, the
least prime `> m`. Witness `n₀ = 10`: `379 → 202`.

**Idea.** V001 fed the Erdős–Turán ruler Bertrand's *worst-case* prime `p ≤ 2m`, losing a
factor 2. Here the record computes the prime itself — `nextPrime m` is a `List.find?` over
the offsets `0, …, m`, so it is plain `Nat` arithmetic that the kernel evaluates cheaply
(`decide +kernel` settles the witness comparison well inside the fuel budget). The value
found is prime by `List.find?_some`, and the `none` branch is ruled out by Bertrand: the
prime `p ∈ (m, 2m]` sits at offset `p − m − 1 ≤ m` in the searched range. The ruler and its
Sidon property are V001's `etRuler_mem`, reused unchanged (`based-on = ["V001"]`).

**Why.** It improves the record at every `m ≥ 2` with `nextPrime m < 2m` — that is, all `m`
of interest, infinitely many — and roughly halves the bound: `≈ 2m²` instead of `4m²`. Cost:
1707 heartbeats.

## V003 — `baseline claude-opus-5`

**Bound.** `record = min(V002.record, small)` where `small` tabulates the optimal lengths
`f(4) = 6`, `f(7) = 25`, `f(8) = 34`, `f(9) = 44`, `f(10) = 55`, `f(11) = 72` and is the
previous record elsewhere. Witness `n₀ = 10`: `202 → 55`.

**Idea.** Both general constructions are still far off for small `m` (the binary ruler gives
`63` at `m = 7`, the Erdős–Turán ruler `269` at `m = 11`), so each table entry is witnessed
by an explicit optimal ruler from OEIS A003022 — e.g. `{0,1,4,10,18,23,25}` at `m = 7`,
`{0,1,4,13,28,33,47,54,64,70,72}` at `m = 11` — and the four `RulerLengths` conditions are
checked by `decide +kernel`. No search happens in the proof: the rulers are given data.

**Why.** An improvement at only six points, chosen because the record is now exact there —
these six values are optimal, so they can never be improved again. `m = 12, 13` were
prepared too (`{0,2,6,24,29,40,43,55,68,75,76,85}` and
`{0,2,5,25,37,43,59,70,85,89,98,99,106}`) but the Sidon check is `Θ(m⁴)` quadruples and the
pair pushed the file past the 200000-heartbeat budget; with `m ≤ 11` the file costs 46634.

## V004 — `baseline claude-opus-5`

**Bound.** `record = min(V003.record, small)` where `small` tabulates the optimal lengths
`f(12) = 85`, `f(13) = 106`, `f(14) = 127`, `f(15) = 151`. Witness `n₀ = 12`: `290 → 85`.

**Idea.** Exactly V003's idiom, continued: each entry is an explicit optimal ruler from
OEIS A003022 and the four `RulerLengths` conditions are checked by `decide +kernel`. The
rulers are

- `m = 12`: `{0,2,6,24,29,40,43,55,68,75,76,85}`
- `m = 13`: `{0,2,5,25,37,43,59,70,85,89,98,99,106}`
- `m = 14`: `{0,4,6,20,35,52,59,77,78,86,89,99,122,127}`
- `m = 15`: `{0,4,20,30,57,59,62,76,100,111,123,136,144,145,151}`

**Why.** The Erdős–Turán ruler is still roughly 3.4× too long here (`481` against
`f(15) = 151`), and these four values are *optimal*, so the record becomes exact at them
and can never be improved there again. V003's report had flagged `m = 12, 13` as
budget-blocked; they are not, once the already-proved entries `m ≤ 11` are left to the
fallback instead of being re-proved. That is the whole trick of this version: a new
version only pays for its *new* entries, since `small` delegates everywhere else.

Cost: 141206 heartbeats of 200000, essentially all in `small_valid`. The four entries cost
`≈ 1.02` heartbeats per quadruple of `IsSidon`, i.e. `≈ m⁴` each; `m = 16` would have added
another `67000` and overflowed.

## V005 — `baseline claude-opus-5`

**Bound.** `record = min(V004.record, small)` with `f(16) = 177` and `f(17) = 199`.
Witness `n₀ = 16`: `514 → 177`.

**Idea and why.** As V004. Rulers `{0,1,4,11,26,32,56,68,76,115,117,134,150,163,168,177}`
and `{0,5,7,17,52,56,67,80,81,100,122,138,159,165,168,191,199}`. Two entries are what the
budget holds at this size: 146107 heartbeats of 200000, `≈ 0.98` per `IsSidon` quadruple.

## V006 — `trial claude-fable`

**Bound.** `record = min(V005.record, ruzsaLen)` with `ruzsaLen m = p(p−1) − 1`, `p = nextPrime m`
(V002's least prime above `m`). Witness `n₀ = 18`: `650 → 341`.

**Idea.** Ruzsa's ruler modulo `p(p−1)`: the mark of index `i < p − 1` is
`(p·i + (p−1)·val(gⁱ)) mod p(p−1)`, the residue that is `i` modulo `p − 1` and `−gⁱ` modulo
`p`, for a generator `g` of `(ZMod p)ˣ`. If `aᵢ + aⱼ = aₖ + aₗ` in `ℕ`, reducing modulo
`p − 1` gives `i + j ≡ k + l`, hence `gⁱgʲ = gᵏgˡ` because `g` has order `p − 1`
(`pow_eq_pow_iff_modEq`); reducing modulo `p` gives `gⁱ + gʲ = gᵏ + gˡ`; so
`(gⁱ − gᵏ)(gⁱ − gˡ) = 0` in the field `ZMod p`, and `pow_injOn_Iio_orderOf` turns equal
powers into equal indices. The marks are distinct because the index is the mark modulo
`p − 1`, so there are `p − 1 ≥ m` of them, all below `p(p−1)`. A general lemma
`f_le_of_sidon` (any Sidon set with `≥ m` elements below `N` gives `f m ≤ N − 1`, via an
`m`-element subset and its maximum) finishes.

**Why.** It is `≈ m²` where the record was `≈ 2m²`, so it improves the record at **every**
`m ≥ 18`, and it needs no finite-field extension, unlike Bose–Chowla and Singer. Proof about
150 lines, 12980 heartbeats.

## V007 — `trial claude-fable`

**Bound.** `record = min(V006.record, small)` where `small` tabulates the optimal lengths
`f(18) = 216, f(19) = 246, f(20) = 283, f(21) = 333, f(22) = 356, f(23) = 372, f(24) = 425,
f(25) = 480, f(26) = 492, f(27) = 553, f(28) = 585` and is the previous record elsewhere.
Witness `n₀ = 28`: `811 → 585`. The record is now **exact at every `m ≤ 28`**, i.e. at every
`m` where `f` is known.

**Idea.** The rulers are the optimal ones of Wikipedia's *Golomb ruler* table (Dollas–Rankin–
McCracken for `m ≤ 19`, distributed.net OGR-20 … OGR-28); the 28-mark ruler is the 27-mark
one with `585` appended. What made all eleven fit in one version is a new checker:
`sidonCheck` walks the list and, for each mark `a`, inserts the sums `a + b` (`b` at or
after `a`) into a `Nat` bitset, failing on a repeat. `testBit`, `|||`, `<<<` are
GMP-accelerated in the kernel, so the check is `≈ m²` cheap operations: the 28-mark ruler
costs 873 heartbeats, against `≈ m⁴ ≈ 600k` for `decide` on `IsSidon`. `sidonCheck_spec`
proves once, by induction on the list with the bitset abstracted as the `Set ℕ` it
represents, that a passing check gives the Sidon property; `f_le_of_rulerCheck` packages the
four `RulerLengths` conditions, so each entry is one `decide +kernel`.

**Why.** This is route 1 of the previous report, in one version rather than five, and the
values are optimal, so they can never be improved again. Cost: 13561 heartbeats.

**Trap found.** Discharging the eleven-way `if` chain with `unfold small; split_ifs` cost
175k heartbeats by itself (nested `split`: 85k) and nearly broke the budget; a chain of
`by_cases m = 18; subst` with the entries as separate theorems costs 583. Later versions
adding table entries should use that form.

## V008 — `trial claude-fable`

**Bound.** `record = min(V007.record, winLen)` with `winLen m = (m−1)·p`, `p = nextPrime m`.
Witness `n₀ = 29`: `929 → 868`. Improves at every `m ≥ 29`.

**Idea.** Ruzsa's set is Sidon *modulo* `n = p(p−1)` with `k = p − 1` residues, so it may be
rotated. Double counting over the `n` cyclic windows `[t, t+L]`: each residue lies in `L + 1`
of them, so some window holds at least `m` residues as soon as `(m−1)n < k(L+1)`; with
`n/k = p` the window `L = (m−1)p` works. The `m` residues in it, after rotation, are an
`m`-mark ruler of length `≤ L`: an equality of sums of rotated residues is a congruence of the
original sums modulo `n`. In Lean this is `window_exists` (Mathlib's pigeonhole
`exists_lt_card_fiber_of_mul_lt_card_of_maps_to` on pairs `(x, j)` mapped to `t ≡ j − x`) and
`f_le_of_sidonMod`, a generic lemma: any Sidon set modulo `n` with `k` residues gives
`f m ≤ ⌊(m−1)n/k⌋`. `ruzsaRuler_sidonMod` is V006's proof with congruences.

**Why.** `p(p−1) − 1 → (m−1)p` saves `p(p−m) − 1` at every `m ≥ 29`, and the generic lemma
is what Bose–Chowla and Singer will plug into next. Cost: 14209 heartbeats.

## V009 — `trial claude-fable`

**Bound.** `record = min(V008.record, bcLen)` with `bcLen m = ⌊(m−1)(p²−1)/p⌋`, `p = primeGe m`
the least prime `≥ m`. Witness `n₀ = 31`: `1110 → 929`. Improves at every `m ≥ 29`: by about
`3m` at prime `m`, by one elsewhere.

**Idea.** Bose–Chowla in `GaloisField p 2`: for a generator `θ` of the units (order `p² − 1`),
the `p` discrete logarithms of `θ + c`, `c ∈ GF(p)`, are Sidon modulo `p² − 1`, because
`(θ + x)(θ + y) = (θ + z)(θ + w)` forces `x + y = z + w` and `xy = zw` once `1, θ` are known
to be independent over `GF(p)` — which holds since `θ ∈ GF(p)` would give `θ^(p−1) = 1`.
Plugged into V008's window lemma with `n = p² − 1`, `k = p`.

**Why.** At prime `m` V008 had to use the next prime; here `m` is its own `p`. Mathlib has
everything needed for `GF(p²)` (`GaloisField`, cyclic units, `GaloisField.card`), so the
formalisation is 130 lines and compiled first time. Cost: 21271 heartbeats.

## V010 — `trial claude-fable`

**Bound.** `record = min(V009.record, singerLen)` with `singerLen m = (m−1)·q`, `q = primeGe (m−1)`
the least prime `≥ m − 1`. Witness `n₀ = 30`: `898 → 841`. Improves at every `m = q + 1`,
`q ≥ 29` prime, by at least `m − 1`.

**Idea.** Singer in `GaloisField p 3`: with `θ` a generator of the units (order
`p³ − 1 = (p² + p + 1)(p − 1)`), the residues `a < p² + p + 1` with `θᵃ ∈ GF(p) + GF(p)θ` —
namely `0` and `dlog(θ + c) mod (p²+p+1)` — are `p + 1` residues Sidon modulo `p² + p + 1`.
The proof needs: units with `x^(p−1) = 1` are the prime field (counting in the cyclic group,
`IsCyclic.card_pow_eq_one_le`); `1, θ, θ²` independent (else `p³ − 1 ≤ p²`); and `θᵃ = μθᵇ`
with `μ ∈ GF(p)ˣ` forces `a = b` below `p² + p + 1`. The Sidon step compares coefficients of
`θᵃθᵇ = μ θᶜθᵈ` and uses the identity `μ(xₐy_c − yₐx_c)(xₐy_d − yₐx_d) = 0` instead of unique
factorisation. Window lemma with `n = p² + p + 1`, `k = p + 1`, `L = (m−1)p`.

**Why.** It is the classical `m² − m`-type bound at `m = p + 1`, the last of the three
constructions, and completes the picture: the record is now `(m−1)·q` with `q` the least
prime `≥ m − 1` (minus one when `q ≥ m`, from V009). Cost: 64713 heartbeats.

## V011 — `trial claude-fable`

**Bound.** `record = min(V010.record, singerPPLen)` with `singerPPLen m = (m−1)·q`,
`q = primePowGe (m−1)` the least prime *power* `≥ m − 1`. Witness `n₀ = 33`: `1183 → 1024`.
Improves wherever the least prime power `≥ m − 1` is a non-prime smaller than the least prime:
`m = 33, 49, 50, 63–65, 81, 82, 115–126, 129, …` — infinitely many `m`.

**Idea.** V010's Singer proof restated over an arbitrary finite field `K` (`|K| = q`) with a
ring homomorphism into `L` (`|L| = q³`): the only facts about `ZMod p` it used were `|K| = q`,
Lagrange `x^(q−1) = 1`, and injectivity of the embedding. Instantiated with
`K = GaloisField p k`, `L = GaloisField p (3k)` and Mathlib's
`FiniteField.nonempty_algHom_of_finrank_dvd`. The record searches for the least prime power
with Mathlib's decidable `IsPrimePow`, which the kernel evaluates cheaply.

**Why.** Prime powers are the remaining classical parameters; with them the record is
`(m−1)·q`, `q` the least prime power `≥ m − 1`, which is the literature's general bound
(`m² + O(m·gap)`). Cost: 60498 heartbeats.

## V012 — `trial claude-fable`

**Bound.** `record = min(V011.record, small)` where `small` tabulates the best known lengths
for `m = 29, …, 80` (Rokicki–Dogon, `cube20.org/golomb`): `623, 680, 747, 784, 859, 938, 987,
1005, 1099, 1146, 1252, 1282, 1305, 1397, 1507, 1596, 1687, 1703, 1804, 1887, 1958, 2094, 2190,
2270, 2347, 2373, 2598, 2725, 2773, 2851, 2911, 3019, 3134, 3215, 3391, 3527, 3593, 3757, 3819,
3956, 4145, 4217, 4330, 4473, 4513, 4753, 4982, 5089, 5204, 5299, 5408, 5563`. Witness
`n₀ = 29`: `811 → 623`. Improves at all 52 values, by 11–25 %.

**Idea.** The general bound `(m−1)·q` is the *average* window of a Singer/Bose modular ruler;
the *best* window over all multipliers and rotations is much shorter, and Rokicki and Dogon
have tabulated it (with the ruler) for every `m` up to 40000. For `m ≤ 80` each ruler is
data the kernel checks in `≈ 0.92 m²` heartbeats with V007's bitset checker; 52 entries cost
163k of the 200k budget. The rulers were downloaded, re-verified in Python and typeset into
`Proof.lean` by a script; an independent re-derivation of the windows for `q ≤ 61` matched
all 34 comparable entries.

**Why.** Improvement at 52 consecutive `m`, each by hundreds; none of these values is known
to be optimal, so they may be improved again, but not by any known construction.

## V013 — `trial claude-fable`

**Bound.** `record = min(V012.record, small)` where `small` tabulates the best known lengths
for `m = 81, …, 100` (Rokicki–Dogon): `5717, 5814, 6020, 6159, 6410, 6537, 6708, 6745, 6778,
6967, 7542, 7617, 7726, 7884, 7967, 8121, 8357, 8462, 8540, 8831`. Witness `n₀ = 81`:
`6480 → 5717`. Improves at all 20 values, by 10–15 %.

**Idea and why.** The continuation of V012; each entry costs `≈ 0.92 m²` heartbeats with
V007's checker (`f100`: 8652), 146k in all, so this is the last block that checker can hold
in one version. Same generator script, nothing new proved.

## Values

| m | 5 | 7 | 10 | 11 | 13 | 15 | 17 | 18 | 20 | 24 | 28 | 29 | 30 | 31 | 100 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| V000 (seed) | 11 | 63 | 511 | 1023 | 4095 | 16383 | 65535 | 11305 | 15561 | 27025 | 43065 | 47880 | 53041 | 58560 | 1989801 |
| V003 | 11 | 25 | 55 | 72 | 416 | 481 | 577 | 650 | 890 | 1341 | 1570 | 1745 | 1802 | 2232 | 20002 |
| V005 | 11 | 25 | 55 | 72 | 106 | 151 | 199 | 650 | 890 | 1341 | 1570 | 1745 | 1802 | 2232 | 20002 |
| V006 | 11 | 25 | 55 | 72 | 106 | 151 | 199 | 341 | 505 | 811 | 811 | 929 | 929 | 1331 | 10099 |
| V007 | 11 | 25 | 55 | 72 | 106 | 151 | 199 | 216 | 283 | 425 | 585 | 929 | 929 | 1331 | 10099 |
| V008 | 11 | 25 | 55 | 72 | 106 | 151 | 199 | 216 | 283 | 425 | 585 | 868 | 899 | 1110 | 9999 |
| V009 | 11 | 25 | 55 | 72 | 106 | 151 | 199 | 216 | 283 | 425 | 585 | 811 | 898 | 929 | 9998 |
| V010 | 11 | 25 | 55 | 72 | 106 | 151 | 199 | 216 | 283 | 425 | 585 | 811 | 841 | 929 | 9998 |
| V011 | 11 | 25 | 55 | 72 | 106 | 151 | 199 | 216 | 283 | 425 | 585 | 811 | 841 | 929 | 9998 |
| V012 | 11 | 25 | 55 | 72 | 106 | 151 | 199 | 216 | 283 | 425 | 585 | 623 | 680 | 747 | 9998 |
| V013 | 11 | 25 | 55 | 72 | 106 | 151 | 199 | 216 | 283 | 425 | 585 | 623 | 680 | 747 | 8831 |
| f(m) (known) | 11 | 25 | 55 | 72 | 106 | 151 | 199 | 216 | 283 | 425 | 585 | — | — | — | — |

(All values above were evaluated with `#eval`; the V003/V005 values at `m = 20, 30, 100` in
the previous version of this table — `1004`, `2262`, `20398` — were miscomputed.)

The record is now **exact** for every `m ≤ 28` (all known values), equal to the **best known**
ruler for `29 ≤ m ≤ 100`, and `min((m−1)·q, ⌊(m−1)(p²−1)/p⌋)` beyond, with `q` the least
prime power `≥ m − 1` and `p` the least prime `≥ m` — the literature's general bound
`m² + O(m · prime gap)`.

## Next improvement

**Where the record stands.** `m ≤ 28` exact; `29 ≤ m ≤ 100` the best known rulers (not known
to be optimal, and no construction is known to beat them); `m > 100` the general
`(m−1)·q` (Singer, `q` least prime power `≥ m − 1`), minus one where Bose–Chowla's
`⌊(m−1)(p²−1)/p⌋` with `p` the least prime `≥ m` is smaller. Every classical construction
(Erdős–Turán, Ruzsa, Bose–Chowla, Singer, over primes and prime powers) is now formalised in
`Records/Upper/V001`–`V011`, together with the generic window lemma.

Routes, in increasing order of effort:

1. **Extend the table of best known rulers past `m = 100`.** The data exists for every `m`
   up to 40000 (Rokicki–Dogon), and the generator script
   `.lake/scratch/Golomb-Upper/fable/search/gen.py` (usage: `gen.py <mmin> <mmax> V<k> V<k-1>`,
   reads `golomb-all-00` and `rulers-all-00` in the same directory, verifies each ruler and
   writes `Def.lean`, `Proof.lean`, `metadata.toml`) produces a version in one command. The
   obstacle is cost: V007's `rulerCheck` inserts the `m(m+1)/2` sums into a `Nat` bitset one
   by one, `≈ 0.92 m²` heartbeats per ruler, so with the 200k budget the next block would be
   `m = 101, …, 118` or so, and the blocks shrink as `m` grows — many small versions.
2. **An `O(m)` checker (unfinished; started in `.lake/scratch/Golomb-Upper/fable/fast1.lean`).**
   For a *sorted* list with bitset `B = Σ 2^x`, the row of sums `a + b` (`b ≥ a`) is the single
   shifted bitset `(B >>> a) <<< (2a)`: so the Sidon check is `m` iterations of
   `mask &&& row = 0; mask := mask ||| row` — a few GMP-accelerated operations per mark, i.e.
   `O(m)` kernel steps instead of `O(m²)` — plus a `Chain' (· < ·)` sortedness check. With it a
   version could hold hundreds of rulers (the 1 MB directory limit, ≈ 5–6 bytes per mark,
   becomes the constraint: `m = 101, …, 300` is about 250 KB). The scratch file contains the
   definitions (`bits`, `rows`, `fastCheck`) and `decide +kernel` tests on the 28-, 100-,
   200-, 300- and 500-mark rulers; the budget probe reported that **the definition of
   `fastCheck` itself failed to elaborate within 200k heartbeats**, not yet diagnosed
   (suspects: the `decide (List.Chain' (· < ·) l)` instance, or the `match … with | 0 | _ + 1`
   on a `Nat`; try `l.Sorted`-free formulations such as an explicit adjacent-pairs loop, and
   `Bool` `cond` instead of `match`/`if`). The reasoning lemma to write is the analogue of
   V007's `sidonCheck_spec`: with `l' = P ++ l` and `mask` representing
   `{x + y : x ∈ P, y ∈ l', x ≤ y}`, a passing row `a` gives `a + b ≠ x + y` for all `x ∈ P`,
   `b ≥ a`, `y ≥ x`, hence injectivity of `(x, y) ↦ x + y` on ordered pairs of a sorted list
   (`List.Pairwise`, then `List.Pairwise.forall` with symmetry), hence `IsSidon`; the bit
   lemmas are `Nat.testBit_shiftLeft`, `Nat.testBit_shiftRight`, `Nat.testBit_and`,
   `Nat.testBit_or`, `Nat.eq_of_testBit_eq`. Also, with hundreds of entries the `by_cases`
   chain for `small` must be split into blocks of ≈ 50 (its cost grows superlinearly: 20
   cases 1.3k, 52 cases 5.7k heartbeats), each block delegating to the next.
3. **Bose–Chowla over prime powers.** V009's proof generalises exactly as V011 generalised
   V010 (`K` with `q` elements inside `L` with `q²`, `k ∣ 2k`); it gains one at every
   `m = q` with `q` a non-prime prime power (`m = 32, 49, 64, 81, 121, …`): infinitely many
   `m`, but by one each. About an hour.
4. **Below the best known rulers.** For `m ≥ 29` nothing better than the tabulated windows
   is known; a genuinely new idea would be needed, and the lower record (`≈ m² − 2m^{3/2}`)
   shows there is only a factor `≈ 1.25` of room at `m ≈ 100`.

**Problems hit (this run).** (i) `unfold small; split_ifs` on an 11-way `if` chain cost 175k
heartbeats (nested `split`: 85k); `by_cases m = k; subst` with the entries as separate
theorems costs a few hundred — use that. (ii) `rcases … with rfl` in a case split substituted
the wrong variable; name the equations and `rw`. (iii) `Nat.ModEq.mul_right` keeps the
modulus, `mul_right'` scales it. (iv) `Finset.image` needs `DecidableEq`: `classical`.
(v) The earlier report's table values at `m = 20, 30, 100` were miscomputed; evaluate with
`#eval` before quoting a value. (vi) Own Python search over `GF(q³)` for prime powers with
`k ≥ 2` was too slow with brute-force irreducible polynomials and full field enumeration
(`.lake/scratch/Golomb-Upper/fable/search/gf.py`, `search.py`); it was only used as a
cross-check for `q ≤ 61` and is not needed since the published rulers cover all `m`.
