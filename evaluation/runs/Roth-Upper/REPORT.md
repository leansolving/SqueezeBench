# Roth `r₃(n)` — upper-bound track

Submitters of the versions below: **`baseline claude-opus-5`** (V001–V004) and
**`trial claude-fable`** (V005 onwards).

`f n = r₃(n)` is the largest size of a 3-AP-free subset of `{0, …, n-1}` (OEIS
[A003002](https://oeis.org/A003002)), pinned to `0` below `nMin = 1`.

## What is known

- **Trivial / starting record.** `r₃(n) ≤ n` (Mathlib `rothNumberNat_le`), the seed `V000`.
- **Roth's theorem.** `r₃(n) = o(n)` (Roth, *On certain sets of integers*, J. London Math.
  Soc. 28 (1953) 104–109). Mathlib has it (`Mathlib/Combinatorics/Additive/Corner/Roth.lean`)
  but only as a `=o[atTop]` statement: it is non-effective as stated, so no computable
  record can be extracted from it without redoing the quantitative work.
- **Best known.** `r₃(n) ≪ n / (log n)^{1+c}` for an absolute `c > 0` (Bloom–Sisask,
  *Breaking the logarithmic barrier in Roth's theorem on arithmetic progressions*,
  arXiv:2007.03528, 2020); refined to `exp(-c (log n)^{1/9}) n` by Kelley–Meka
  (*Strong bounds for 3-progressions*, arXiv:2302.05537, 2023) and Bloom–Sisask
  (arXiv:2309.02353). These are far out of reach of formalisation today.
- **Lower bound (for context).** Behrend, `n · exp(-c √(log n))`, so the truth is `n^{1-o(1)}`:
  no bound of the shape `c·n` with `c < 1` can be far from optimal in exponent, but every
  constant factor is still open territory for a formalised record.
- **Elementary bounds with a constant below `1`.** Erdős and Turán (*On some sequences of
  integers*, J. London Math. Soc. 11 (1936) 261–264) proved `r₃(2m) ≤ m` for `m ≥ 8` from
  `r₃(8) = 4`, `r₃(10) = 5`, `r₃(12) = 6` and subadditivity, and the *doubling step*
  `r₃(2m+1) ≤ 2 r₃(m)`: a 3-AP-free subset of `[0, 2m]` misses an endpoint, or contains both
  and hence misses their midpoint `m`. Iterated, `r₃((b+1)2ᵏ - 1) ≤ 2ᵏ r₃(b)`, so any exact
  value `r₃(b)` gives the asymptotic constant `r₃(b)/(b+1)`: `4/9` from `r₃(8) = 4`, `3/8` from
  `r₃(23) = 9` (their announced `3/8 + ε`). Moser (*On non-averaging sets of integers*, Canad.
  J. Math. 5 (1953) 245–252) proved `r₃(n) < 2n/5 + 3` by counting pairwise sums of a parity
  class (a 3-AP-free `t`-set has at least `3t - 7` distinct pairwise sums) and, with a longer
  case analysis, `r₃(n) < 4n/11 + 5`. These are the only elementary (pre-Roth) constants we
  know of; everything better is Roth-type Fourier analysis.
- **Exact small values** (A003002, reporting only; not a source of theorems here):

  | n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 17 | 20 | 22 | 24 | 28 | 32 | 40 | 50 | 64 | 100 |
  |---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
  | r₃(n) | 1 | 2 | 2 | 3 | 4 | 4 | 4 | 4 | 5 | 5 | 6 | 6 | 7 | 8 | 8 | 9 | 9 | 10 | 11 | 13 | 15 | 16 | 20 | 27 |

  Extremal sets are few: `r₃(14) = 8` only by `{0,1,3,4,9,10,12,13}`, `r₃(20) = 9` by two sets,
  `r₃(24) = 10` by two (local enumeration). The minimum number of distinct pairwise sums of a
  3-AP-free `t`-set (over `t`-subsets of `[0, 2.6t + 3)`) is `9, 12, 16, 19, 25, 30, 35, 40, 47`
  for `t = 5, …, 13`: slope about `5` from `t = 9` on, against Moser's `3t - 7`.

  The best "density" a small exact value can give through subadditivity is `r₃(8) = 4`
  (ratio `1/2`), then `r₃(28) = 11` (ratio `11/28 ≈ 0.393`).

### The constraint that shapes this track

`Def.lean` checks `f 4 = 3` with `set_option maxRecDepth 1000000`, and `Proof.lean` may set
**no** options and must stay inside 200000 heartbeats. So `rothNumberNat` cannot be evaluated
in a record proof at all — not even at `n = 3`. Every value used has to be proved by hand from
`rothNumberNat_spec` / `ThreeAPFree`, which rules out the "compute `r₃(8) = 4`, then use
subadditivity" route that a paper argument would take.

## V001 — `baseline claude-opus-5`

**Bound.** `record n = min (n, 2 * ⌈n/3⌉)`, i.e. `minWith V000.record (fun n => 2*((n+2)/3))`.

**Idea.** `{a, a+1, a+2}` is itself a 3-AP, so `r₃(3) ≤ 2`; concretely, the only 3-element
subset of `range 3` is `range 3`, which is not `ThreeAPFree` (`0 + 2 = 1 + 1`). Mathlib's
subadditivity `rothNumberNat_add_le` then gives `r₃(3k) ≤ 2k` by induction on `k`, and
monotonicity of `rothNumberNat` lifts it to every `n ≤ 3⌈n/3⌉`.

**Why.** It is the cheapest bound that improves the seed at every `n ≥ 3` except `n = 4`
(asymptotic ratio `2/3` instead of `1`), and it needs no evaluation of `rothNumberNat`.

**Witness.** `n₀ = 3`: `3 → 2` (and `r₃(3) = 2`, so the record is exact there).

## V002 — `baseline claude-opus-5`

**Bound.** `record n = min (V001.record n, (n+3)/2)`, asymptotic ratio `1/2`.

**Idea.** A sumset/parity count. Let `S ⊆ [0,n)` be 3-AP-free, `k = |S|`, and let `A` be the
elements of `S` in one parity class, `e = |A|`, with `b = min A`, `c = max A`. Put

* `X = { (b+a)/2 : a ∈ A \ {b} }`, `Y = { (c+a)/2 : a ∈ A \ {c} }`.

All the sums are even, so halving is injective, and `X`, `Y ⊆ [0,n)`. 3-AP-freeness says
`b + a = 2t` with `t ∈ S` forces `a = b`, so `X` and `Y` are disjoint from `S` itself.
Finally `b+a ≤ b+c ≤ c+a'`, so `X ∩ Y ⊆ {(b+c)/2}`. Counting `S ∪ X ∪ Y ⊆ [0,n)` gives
`k + (e-1) + (e-2) ≤ n`, i.e. `k + 2e ≤ n + 3`. Summing over the two parity classes
(`e₀ + e₁ = k`) gives `4k ≤ 2n + 6`, so `r₃(n) ≤ (n+3)/2`.

**Why.** It beats V001 at `n = 4, 7, 8` and at every `n ≥ 10`, and improves the asymptotic
constant from `2/3` to `1/2` — the best constant reachable from a small exact value
(`r₃(8) = 4`), but obtained without ever evaluating `rothNumberNat`.

**Witness.** `n₀ = 8`: `6 → 5`.

## V003 — `baseline claude-opus-5`

**Bound.** `record n = min (V002.record n, v n)` with

    v n = (n+2)/2 + (n+3)/4 - (n+2)/4     -- = 2*(n/4) + 1 if 4 ∣ n, else 2*(n/4) + 2

i.e. `⌊(n+3)/2⌋` for `n ≢ 3 (mod 4)` and `⌊(n+1)/2⌋` for `n ≡ 3 (mod 4)`:
`1, 2, 2, 2, 3, 4, 4, 4, 5, 6, 6, 6, 7, …`

**Idea — the integrality V002 threw away.** V002 proves `key`: for a 3-AP-free `S ⊆ [0,n)`
with `k = |S|` and *either* parity class `A_r` of size `e_r`,

    k + 2 e_r ≤ n + 3 ,      e₀ + e₁ = k .

V002 then *averages* the two instances, getting `4k ≤ 2n + 6`, i.e. `2k ≤ n + 3`. The average
is attained only at `e₀ = e₁ = k/2`, which is impossible when `k` is odd. Keeping the
integrality: the larger class has `e ≥ ⌈k/2⌉`, so

* `k` even → `2k ≤ n + 3`;
* `k` odd  → `k + (k+1) ≤ n + 3`, i.e. `2k ≤ n + 2`.

For `n ≡ 3 (mod 4)` the previous ceiling `(n+3)/2` is **odd**, so it is excluded by the second
line and `k ≤ (n+1)/2`. This is a gain of `1` at every `n ≡ 3 (mod 4)`, `n ≥ 7` — a quarter of
all `n`, infinitely many. It is sharp at `n = 3, 7, 11, 15` (where `r₃(n) = 2, 4, 6, 8`).

**Cost.** Nothing new is proved about `r₃`: V003 imports `V002.key` unchanged and replaces the
averaging step by `arith`, a four-way case split (parity of `k` × which class is larger)
closed by `omega`. 6700 heartbeats in all.

**Witness.** `n₀ = 7`: `5 → 4` (and `r₃(7) = 4`, so the record is exact there).

## V004 — `baseline claude-opus-5`

**Bound.** `record n = min (V003.record n, 4 ⌊n/8⌋ + V003.record (n mod 8))`.

**Idea.** The route recommended after V003: `r₃(8) ≤ 4` proved by hand (`roth8`: with five
points in `[0, 8)` the V002 count forces parity classes of sizes `2` and `3`; the 3-class is a
3-AP-free 3-subset of a 4-term progression, its three midpoints pin the other class down, and
each of the four cases contains a 3-AP), then `rothNumberNat_add_le` iterated on blocks of
eight (`step`). Gain of `1` at `n ≡ 0, 1 (mod 8)`.

**Witness.** `n₀ = 8`: `5 → 4`. Cost 12.6k heartbeats. (This section was added by
`trial claude-fable` from the record's files; V004 has no `REPORT.md` of its own.)

## V005 — `trial claude-fable`

**Bound.** `record n = patch (min (V004.record n) (min (half n) (moser n))) 17 8` with

    half n  = if n < 8 ∨ n = 14 then n else (n + 1) / 2
    moser n = max (2 ⌊(n+7)/5⌋, 2 ⌊(n+3)/5⌋ + 1)

i.e. `⌈n/2⌉` for all `n ≥ 8` except `14`, `r₃(17) ≤ 8`, and Moser's `2n/5 + O(1)`, which takes
over at `n = 21`. Asymptotic constant `2/5` instead of `1/2`; `100 → 42`, `1000 → 402`.

**Idea.** Three ingredients, all cheap (55k heartbeats in all).

1. *Windows.* Mathlib's `addRothNumber_Ico` gives `|S ∩ [a, a+m)| ≤ r₃(m)` for every
   3-AP-free `S` (`win`), and unit windows `[a, a+1)` tie counts to membership, so `omega` does
   the bookkeeping. With `r₃(8) ≤ 4`: six points in `[0,10)` force `0, 1, 8, 9 ∈ S`, hence
   `S = {0,1,3,6,8,9} ∋ 0,3,6`, so `r₃(10) ≤ 5`; seven points in `[0,12)` force three in `[0,4)`
   and three in `[8,12)`, hence `0, 3, 8, 11 ∈ S`, which empties `[4,8)`, so `r₃(12) ≤ 6`.
   Blocks of `8, 10, 12` (and `13 = 12 + 1`, `22 = 10 + 12` for the residues `5, 6 (mod 8)`)
   give `r₃(n) ≤ ⌈n/2⌉` for `n ≥ 8`, `n ≠ 14` (`half_valid`).
2. *Doubling* (`roth_odd`): `r₃(2m+1) ≤ 2 r₃(m)` for `m ≥ 1`, so `r₃(17) ≤ 8`.
3. *Moser's count* (`moser_index`, `moser_sums`, `key`, `moser_valid`). For a 3-AP-free
   `A = {a₀ < … < a_{t-1}}` the sums `aᵢ + aᵢ₊₁`, `aᵢ + aᵢ₊₂` interleave strictly (`chain`,
   `2t - 3` values), and for `i ≤ t - 5` one of `aᵢ + aᵢ₊₃`, `aᵢ + aᵢ₊₄` is outside the chain
   (`between₁`, `between₂`: the first can only be `aᵢ₊₁ + aᵢ₊₂`, and then the second would
   complete a 3-AP at either possible chain position); these `extra` sums increase with `i`.
   So `|A +̂ A| ≥ 3t - 7`. Applied to the larger parity class (`t ≥ ⌈k/2⌉`) of a 3-AP-free
   `S ⊆ [0,n)`, whose pairwise sums halve to distinct integers below `n` outside `S`:
   `k + 3⌈k/2⌉ ≤ n + 7`, whose largest solution is `moser n` (`moser_arith`).

**Why.** It improves V004 at 84 of the 100 values `n ≤ 100` (all `n ≥ 25`, and
`10, 12, 13, 17, 18, 20, 21, 22`), and at every `n ≥ 25`; the asymptotic constant drops from
`1/2` to `2/5`.

**Witness.** `n₀ = 100`: `51 → 42`.

## V006 — `trial claude-fable`

**Bound.** `record n = min (V005.record n, v n)` with

    v n = max (2 ⌊(2n+20)/11⌋, 2 ⌊(2n+11)/11⌋ + 1)

i.e. Moser's second bound `r₃(n) ≤ 4n/11 + O(1)`: `100 → 40`, `1000 → 366`. Beats V005 from
`n = 27` on, at 62 of the values `n ≤ 100` and at every `n ≥ 49`.

**Idea.** Same counting as V005 (`k + |A +̂ A| ≤ n` for the larger parity class `A`, `|A| = t`),
with the sumset bound improved from `3t - 7` to `2|A +̂ A| ≥ 7t - 20`. The latter is an
induction deleting the two smallest elements: the *seven-point lemma* says that for a
3-AP-free `a₀ < … < a₆`, seven of the sums involving `a₀` or `a₁` are distinct and are not sums
of two of `a₂, …, a₆` (sums with an index `≥ 7` are larger than `a₁ + a₆`, so the lemma applies
inside any longer enumeration); `t ≤ 6` is Moser's `3t - 7`. The seven-point lemma: four sums
`[12] < [13] < [23] < [24]` are new outright; one of `[14], [15]` and one of `[25], [26]` is new
(Moser's interleaving, `u_spec`, `v_spec`); a third comes from `[27]`, `[17]` or `[16]` unless
each coincides with an earlier sum, and then, if neither pair is entirely new, the possible
coincidences form a 128-leaf case tree (`hard`) in which every leaf is closed by the order alone
(88) or by one explicit three-term progression (40). The tree was found with z3 as an external
search tool and is replayed in Lean leaf by leaf. Costs: `seven_new` 35k, `hard` 32k, whole file
101k heartbeats.

The reconstruction of Moser's `4/11` as a deletion lemma came from a consultation (which also
noted that Moser's own disjointness claim for his families `T_i` is not literally true, so the
paper's bookkeeping was not followed); every claim was checked by enumeration first.

**Why.** Asymptotic constant `2/5 → 4/11`, a gain at every large `n`.

**Witness.** `n₀ = 1000`: `402 → 366`.

## V007 — `trial claude-fable`

**Bound.** `record n = min (V006.record n, v n)` with

    v n = max (2 ⌊(2n+18)/11⌋, 2 ⌊(2n+9)/11⌋ + 1)

the V006 bound with its additive constant sharpened (`2|A +̂ A| ≥ 7t - 18` instead of
`7t - 20`): one less than V006 at every `n ≡ 0, 1, 6, 7 (mod 11)` from `n = 22` on (30 of the
values `n ≤ 100`, 356 of `n ≤ 1000`); `100 → 39`, `1000 → 366` (unchanged).

**Idea.** The induction of V006 (seven sums die when the two smallest elements go) with its
true base cases: `|A +̂ A| ≥ 9` for `t = 5` (`five_base`: `[12], [13], [23], [24], [34], [35],
[45]` plus two of `[14], [15], [25]`) and `≥ 12` for `t = 6` (`six_base`: six sums involving
`a₀, a₁` outside the sums of `a₂ … a₅`, which number six unless `[36] = [45]`, and then a seventh
from `[16]`, both `[14], [15]` or both `[25], [26]`, else a 13-leaf tree `hard6`). Moser's two
choices are now proved for enumerations of any length (`u_gen`, `v_gen`). 80k heartbeats.

**Why.** A gain at four in eleven of all `n`, for a modest proof on top of V006.

**Witness.** `n₀ = 100`: `40 → 39`.

## The record at a glance

| n | 3 | 4 | 5 | 7 | 8 | 9 | 11 | 12 | 14 | 15 | 19 | 20 | 23 | 28 | 100 | 1000 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| V000 (seed) | 3 | 4 | 5 | 7 | 8 | 9 | 11 | 12 | 14 | 15 | 19 | 20 | 23 | 28 | 100 | 1000 |
| V002 | 2 | 3 | 4 | 5 | 5 | 6 | 7 | 7 | 8 | 9 | 11 | 11 | 13 | 15 | 51 | 501 |
| V003 | 2 | 3 | 4 | **4** | 5 | 6 | **6** | 7 | 8 | **8** | **10** | 11 | **12** | 15 | 51 | 501 |
| V004 | 2 | 3 | 4 | 4 | **4** | 6 | 6 | 7 | 8 | 8 | 10 | 11 | 12 | 15 | 51 | 500 |
| V005 | 2 | 3 | 4 | 4 | 4 | 6 | 6 | **6** | 8 | 8 | 10 | **10** | 12 | **14** | **42** | **402** |
| V006 | 2 | 3 | 4 | 4 | 4 | 6 | 6 | 6 | 8 | 8 | 10 | 10 | 12 | **13** | **40** | **366** |
| V007 | 2 | 3 | 4 | 4 | 4 | 6 | 6 | 6 | 8 | 8 | 10 | 10 | 12 | **12** | **39** | 366 |
| true `r₃(n)` | 2 | 3 | 4 | 4 | 4 | 5 | 6 | 6 | 8 | 8 | 8 | 9 | 9 | 11 | 27 | — |

| n | 10 | 13 | 16 | 17 | 21 | 22 | 24 | 26 | 32 | 40 | 50 | 64 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| V004 | 6 | 8 | 8 | 9 | 12 | 12 | 12 | 14 | 16 | 20 | 26 | 32 |
| V005 | **5** | **7** | 8 | **8** | **10** | **11** | 12 | **12** | **15** | **18** | **22** | **28** |
| V006 | 5 | 7 | 8 | 8 | 10 | 11 | 12 | 12 | **14** | 18 | **21** | **26** |
| V007 | 5 | 7 | 8 | 8 | 10 | **10** | 12 | 12 | 14 | **17** | **20** | 26 |
| true `r₃(n)` | 5 | 7 | 8 | 8 | 9 | 9 | 10 | 11 | 13 | 15 | 16 | 20 |

V005 is exact at `n = 1, …, 8, 10, 11, 12, 13, 14, 15, 16, 17`; V006 changes nothing below `n = 27`.

## What the next improvement would take (as written after V003; route 1 became V004, routes 1–3 are now superseded by V005)

The `1/2` barrier of the midpoint argument is unchanged; V003 only harvested the integrality
of the *split* between the two parity classes. Priced routes, in order of promise:

1. **`r₃(8) ≤ 4`, then subadditivity.** With `r₃(n) ≤ 4·j + B(n - 8j)` and `B` the V003 bound,
   the best offset `t = n - 8j` gives `n/2 + c(t)` with
   `c = 0, 1/2, 1, 1/2, 1, 3/2, 1, 1/2` for `t = 0, …, 7` (using `r₃(0) = 0`, `r₃(3) ≤ 2`,
   `r₃(t) ≤ v t` elsewhere). Comparing with V003 this is a gain of `1` exactly at
   `n ≡ 0, 1 (mod 8)` — again a quarter of all `n`. **This is the recommended next step.**
   A paper proof (no `decide`; `rothNumberNat 8` is far outside the budget): `key` at `n = 8`
   with `k = 5` forces `e_r ≤ 3`, so `{e₀, e₁} = {2,3}`; the 3-element class sits in
   `{r, r+2, r+4, r+6}` and is 3-AP-free, hence is `{r, r+2, r+6}` or `{r, r+4, r+6}`; its
   three midpoints delete three of the four values of the other parity class, which is then
   forced, and in each of the four cases the forced pair completes a 3-AP:
   `{0,2,6}` → `{5,7}` → `5,6,7`; `{0,4,6}` → `{1,7}` → `1,4,7`;
   `{1,3,7}` → `{0,6}` → `0,3,6`; `{1,5,7}` → `{0,2}` → `0,1,2`.
   The Lean cost is the Finset bookkeeping of "a 3-subset of a 4-element set", not the
   mathematics.
2. **`|A +̂ A| ≥ 2|A| - 2` for 3-AP-free `A`, `|A| ≥ 5`.** `key`'s `-3` is exactly
   `|A +̂ A| ≥ 2|A| - 3`, with equality (Freiman) only for arithmetic progressions once
   `|A| ≥ 5` — and a 3-AP-free set of size `≥ 3` is not an AP. That would give
   `k + 2e ≤ n + 2` and hence `k ≤ (n+1)/2` for **odd** `n`, a gain of `1` at `n ≡ 1 (mod 4)`
   (with `n = 5` excluded by hand: `r₃(5) = 4`). The obstruction is formalising the
   `|A| ≥ 5` case of Freiman's `2k-3` classification; the `|A| = 4` exception is real
   (`A = {0,2,6,8}` is 3-AP-free with `|A +̂ A| = 5`).
3. **Recursing into a parity class** (`e_r ≤ r₃(⌈n/2⌉) ≤ B(⌈n/2⌉)`) was re-checked after V003
   and still gives *exactly* the current bound, never one less, at `n ≡ 0, 1, 2 (mod 4)`. The
   family of arguments has `n/2` as a fixed point; only a genuine exact value (route 1) or a
   sumset gain (route 2) leaves it.
4. **Quantitative Roth.** Unchanged: out of reach.

### Practical notes for whoever follows

* Keep the record in `ℕ` arithmetic and keep the `minWith` chain — the fuel gate evaluates the
  whole chain at the witness by `decide +kernel`, and it is cheap for these forms.
* `rothNumberNat` cannot be evaluated in a record proof at all, not even at `n = 3`:
  `Def.lean` needs `maxRecDepth 1000000` for `f 4 = 3`, while `Proof.lean` may set no options
  and has 200000 heartbeats for the whole file. Every value used must be proved by hand from
  `rothNumberNat_spec` / `ThreeAPFree`.
* `rothNumberNat` is an `OrderHom`, so monotonicity is `rothNumberNat.monotone`;
  subadditivity is `rothNumberNat_add_le`.
* `rothNumberNat_spec n : ∃ t ⊆ range n, #t = rothNumberNat n ∧ ThreeAPFree ↑t` is the only way
  into an upper bound; `ThreeAPFree s` unfolds to
  `∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a + c = b + b → a = b`.
* `V002.key` and `V003.arith` are reusable as they stand: import the previous `Proof.lean` and
  name them fully qualified. V003 costs only 6700 heartbeats in total precisely because it
  re-uses `key` rather than re-proving it.
* Sharpness checks worth keeping in mind (they kill the obvious ideas): the midpoint count
  `|A +̂ A| ≥ 2|A| - 3` is attained by the 3-AP-free set `A = {0,2,6,8}`; `S = {0,1,3,4}` at
  `n = 5` and `S = {0,1,3,4,9,10,12,13}` at `n = 14` make `key` an equality, and in the second
  one `S` and the six midpoints of a parity class *partition* `{0,…,13}`.

## What the next improvement would take (as written after V005; route 1 became V006)

The record is now `min(⌈n/2⌉, 2n/5 + O(1))` with a patch at `17`. Every remaining route
below `2/5` is either a sharper *local* count of pairwise sums or an exact value fed into
the doubling chain. Priced:

1. **Moser's `4/11`** (`r₃(n) < 4n/11 + 5`): amounts to `|A +̂ A| ≥ (7/2) t - C` for 3-AP-free
   `t`-sets, by a longer case analysis on which sums `aᵢ + aⱼ` are new. The scaffolding of V005
   (`chain`, `extra`, `between₁/₂`, `moser_index`) is reusable; what is needed is the second
   family of new sums and an argument that they are pairwise distinct. Asymptotic gain
   `0.4 → 0.364`, and a gain at every large `n`.
2. **A `4t - C` count** would give `n/3 + O(1)`. The data above (minimum sumset sizes
   `25, 30, 35, 40, 47` at `t = 9, …, 13`, slope about `5`) say there is room, but no clean
   argument is known to us; the difficulty is double counting between the extra sums of
   different indices, which Moser avoids by making them increase with `i`.
3. **Exact values into the doubling chain.** `r₃((b+1)2ᵏ - 1) ≤ 2ᵏ r₃(b)` makes any exact
   value `r₃(b) ≤ c` worth the constant `c/(b+1)` at infinitely many `n` (and, with
   subadditivity, `c/(b+1) · n + O(log n)` everywhere): `r₃(20) ≤ 9` gives `9/21 ≈ 0.43`
   (worse than Moser), `r₃(23) ≤ 9` gives `3/8`, `r₃(29) ≤ 11` gives `11/30 ≈ 0.367`,
   `r₃(35) ≤ 13` gives `13/36 ≈ 0.361`, `r₃(39) ≤ 14` gives `0.35`, `r₃(50) ≤ 16` gives
   `16/51 ≈ 0.314`. The obstacle is the finite proof: `r₃(20) ≤ 9` alone needs a case analysis
   over the `24` 3-AP-free 5-subsets of `[0,10)` (parity classes) or an endpoint analysis with
   the length-8/12/17 windows; a consultation produced a 4-endpoint-case outline for it, but
   `r₃(23) ≤ 9` and beyond are much larger.
4. **Quantitative Roth.** Unchanged: out of reach, and would only beat `2n/5` at astronomical `n`.

### Practical notes (updated after V005)

* `V005.win` (`|S ∩ Ico a b| ≤ r₃(b - a)` for 3-AP-free `S`, from `addRothNumber_Ico`),
  `win_add`, `unit_le`, `unit_zero` make finite case analyses cheap: state window counts as
  Finset cardinalities and let `omega` combine them; membership facts are turned into unit
  windows. `roth12` (13k heartbeats) shows the pattern.
* `V005.roth_odd` is the doubling step; `V005.rbound m : rothNumberNat m ≤ V004.record m`
  gives any previous value by `decide` on the record.
* Beware `omega` atoms: `Finset.Ico 8 (8+1)` and `Finset.Ico 8 9`, or `rothNumberNat (12+1)`
  and `rothNumberNat 13`, are different atoms; state helper lemmas with explicit numerals
  (`unit_zero 8 9 rfl h`) or ascribe types (`(rothNumberNat_add_le 12 1 : rothNumberNat 13 ≤ …)`).
* The `sums`/`chain`/`extra` development in `V005` is stated for an arbitrary enumeration
  `a : ℕ → ℕ` strictly increasing on `[0, t)`, with 3-AP-freeness in index form
  (`a i + a k = a j + a j → i = j`); every step is an `omega` call on a handful of monotonicity
  instances, so extending it to more families of sums is mechanical.

## What the next improvement would take (as written after V006; route 2 became V007)

The record is `min(⌈n/2⌉, 2n/5 + O(1), 4n/11 + O(1))` (plus `r₃(17) ≤ 8`). All of it rests on
one inequality, `k + |A +̂ A| ≤ n` for the larger parity class, so the next constant is the next
sumset bound. Measured on 3-AP-free sets (minimum over sets of size `w`, elements in
`[0, 3.2w)`): deleting the `m` smallest elements of a `w`-set kills at least

    m=1: 3 (w ≥ 5)   m=2: 7 (w ≥ 7)   m=3: 10, 11, 12 (w = 8, 9, 10)   m=4: 16, 17, 17 (w = 10, 11, 12)

distinct sums, i.e. `3, 3.5, 4, 4.25` per deleted element; the constant `c` per element gives
`r₃(n) ≤ n/(1 + c/2) + O(1)`: `2/5, 4/11, 1/3, 8/25`. Priced routes:

1. **The `(3, 10)` deletion lemma** (`12` sums die when the three smallest of ten go) gives
   `|A +̂ A| ≥ 4t - 14` and `r₃(n) ≤ (n + 14)/3`: `100 → 38`, `1000 → 338`. The V006 machinery
   (automatic sums below the least remaining sum, Moser-type choices, an assembly lemma with
   abstract "new" predicates, a solver-generated hard-case tree replayed by `rcases`) carries
   over; the nine sums `[12], [13], [23], [14], [24], [34], [15], [25], [35]` are automatically
   new (all below `[45]`) and, by the five-element collision lemma, take at least eight values,
   so four more are needed from the fifteen sums `[i j]`, `i ≤ 3 < 6 ≤ j`. The risk is the size
   of the case tree (the seven-point tree has 128 leaves at about 250 heartbeats each; the file
   budget allows perhaps 500 leaves in all) — measure it with the solver before starting.
2. **The constant.** `2|A +̂ A| ≥ 7t - 18` (bases `9, 12` at `t = 5, 6`, both verified by
   enumeration; the `t = 6` base is a second 56-leaf tree `Hu ∧ Hv ∧ H16 ∧ [36] = [45] → False`)
   improves `v` by one at about two in eleven `n` (first at `n = 22`). Cheap but small.
3. **Doubling chains from exact values** (`r₃(23) ≤ 9`, `r₃(29) ≤ 11`, …): now dominated
   unless the value is at least `r₃(35) ≤ 13` (`13/36 < 4/11`); such finite proofs are large.
4. **Quantitative Roth.** Unchanged.

### Practical notes (updated after V006)

* `V006.hard` is the pattern for solver-found case trees: hypotheses are the disjunctions of
  possible coincidences, the tree is nested `rcases`, leaves are `omega` (order contradictions)
  or `absurd (hfree i j k … (by omega)) (by decide)` (an implied three-term progression). Keep
  `omega`'s context free of *positive* disjunctions (`clear` them; `≠` hypotheses are cheap, a
  positive 6-way disjunction costs a 6-way split per call) and give `interval_cases` an explicit
  bound on each variable (`have hp7 : p < 7 := by omega`).
* Heartbeat counts printed by `#count_heartbeats in` are meaningless for `theorem`s unless
  `set_option Elab.async false` is on (bodies are elaborated in parallel otherwise).
* The Erdős–Turán doubling step `V005.roth_odd`, the window lemmas `V005.win` etc., and
  `V005.moser_index`/`V006.count_index` (index-form sumset bounds for an enumeration `a`
  strictly increasing on `[0, t)`) are the reusable pieces; `V006.count_sums` turns an
  index-form bound into one about `V005.sums A` for a 3-AP-free finset.

## State at the end of the session (after V007)

Accepted this session: V005 (`⌈n/2⌉` closure, `r₃(17) ≤ 8`, Moser `2n/5`), V006 (Moser
`4n/11 + O(1)` via the seven-point deletion lemma), V007 (its constant sharpened). V008 is open;
nothing is left half-written in the record directories.

**Unfinished exploration, and where its files are** (all under `.lake/scratch/Roth-Upper/`,
inside the project; the Lean scratch files are copies in `.lake/scratch/Roth-Upper/lean/`):

* `tree_gen.py` — a generic z3-driven explorer for deletion lemmas: `python3 tree_gen.py m w K`
  builds the case tree proving "deleting the `m` smallest of a 3-AP-free `w`-set kills at least
  `K` distinct sums" (candidates in ascending order; `desc` is much worse). Measured:
  `(2,7,7)`: 29 leaves; `(3,9,11)`: 187 leaves (144 "enough new sums", 43 contradictions);
  `(3,10,12)`: 833 leaves. The trees are saved as `tree_<m>_<w>_<K>_asc.json`. The `(3,10,12)`
  lemma would give `|A +̂ A| ≥ 4t - 14` and `r₃(n) ≤ (n+14)/3` (`100 → 38`, `1000 → 338`), but
  at the V006 cost per leaf (about 250 heartbeats for a contradiction leaf, more for a leaf that
  assembles the new sums) neither tree fits the 200k budget in one file. Ideas not tried: a
  hand-designed top level as in V006 (`9` automatic sums below `[45]` with at least `8` values
  by the five-element collision lemma, Moser-type choices, then a solver tree only for the hard
  case); splitting the lemma over several versions' files (each file has its own 200k).
* `tree7.py`, `tree6.py` — the generators of `V006.hard` and `V007.hard6` (fixed branching
  order over the collision disjunctions; leaves certified by `omega` or one implied 3-AP).
* `deletion.py`, `ends.py`, `ends2.py`, `minsum.py`, `localsum.py`, `collide.py` — the
  enumerations behind the numbers quoted above (minimum sumset sizes, deletion counts, deleting
  from both ends: 2+2 elements of a 9- to 14-set kill at least 16 sums in the searched ranges,
  but that lemma is not local and was not pursued).
* `lean/count.lean`, `lean/seven.lean`, `lean/odd.lean`, `lean/win.lean`, `lean/moser.lean` —
  the scratch developments that became V005–V006 (all superseded by the accepted files).

**Recommended next step.** Either the `(3,10,12)` lemma with a smarter top level and a cheaper
leaf encoding (the prize is `n/3`), or, for a sure but small gain, nothing cheap remains: the
constant of V007 is the best this induction can give from bases at `t ≤ 8` (`|A +̂ A| ≥ 16, 19`
at `t = 7, 8` follow from V007's bases); bases at `t = 9, 10` (`25`, `30`) would give
`7t - 13` / `7t - 10` but are large finite statements.
