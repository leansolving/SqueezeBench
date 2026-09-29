# Roth, upper record, V005

By trial claude-fable.

## The bound

    record n = patch (min (V004.record n) (min (half n) (moser n))) 17 8

with

    half n  = if n < 8 ∨ n = 14 then n else (n + 1) / 2
    moser n = max (2 * ((n + 7) / 5)) (2 * ((n + 3) / 5) + 1)

i.e. `r₃(n) ≤ ⌈n/2⌉` for every `n ≥ 8` except `n = 14`, `r₃(17) ≤ 8`, and Moser's bound
`r₃(n) ≤ max(2⌊(n+7)/5⌋, 2⌊(n+3)/5⌋ + 1)`, which is `2n/5 + O(1)` and takes over from
`n = 21` on (`n = 21 → 10`, `n = 100 → 42`, `n = 1000 → 402`).

## How the bound was obtained

Three ingredients, all elementary.

1. **Windows and two more exact values.** Mathlib's `addRothNumber_Ico` gives the window
   lemma `|S ∩ [a, a+m)| ≤ r₃(m)` for every 3-AP-free `S`. With `r₃(8) ≤ 4` (V004) this
   pins down `r₃(10) ≤ 5` (six points in `[0,10)` force `0, 1, 8, 9 ∈ S`, then
   `S = {0,1,3,6,8,9}`, which contains `0,3,6`) and `r₃(12) ≤ 6` (seven points force three in
   `[0,4)` and three in `[8,12)`, hence `0, 3, 8, 11 ∈ S`, which empties `[4,8)`). Subadditivity
   over blocks of `8, 10, 12` then gives `r₃(n) ≤ ⌈n/2⌉` for `n ≥ 8`, `n ≠ 14`. This is the
   route the V003/V004 reports recommended, and it improves V004 at `n ≡ 2, 4, 5, 6 (mod 8)`.
2. **The Erdős–Turán doubling step** `r₃(2m+1) ≤ 2 r₃(m)` (`m ≥ 1`): a 3-AP-free subset of
   `[0, 2m]` either misses an endpoint, and lies in `2m` consecutive integers, or contains both
   endpoints and therefore misses the midpoint `m`. It gives `r₃(17) ≤ 2 r₃(8) = 8`, the value
   at the patch point (P. Erdős, P. Turán, *On some sequences of integers*, J. London Math.
   Soc. 11 (1936), 261–264).
3. **Moser's bound `r₃(n) ≤ 2n/5 + O(1)`** (L. Moser, *On non-averaging sets of integers*,
   Canad. J. Math. 5 (1953), 245–252). Let `S ⊆ [0,n)` be 3-AP-free, `|S| = k`, and let `A`
   be its larger parity class, `t = |A| ≥ ⌈k/2⌉`, enumerated `a₀ < … < a_{t-1}`. The sums
   `aᵢ + aᵢ₊₁` and `aᵢ + aᵢ₊₂` interleave strictly (`2t - 3` values, the *chain*), and for every
   `i ≤ t - 5` one of `aᵢ + aᵢ₊₃`, `aᵢ + aᵢ₊₄` lies outside the chain: `aᵢ + aᵢ₊₃` is strictly
   between `aᵢ + aᵢ₊₂` and `aᵢ₊₁ + aᵢ₊₃`, so in the chain it equals `aᵢ₊₁ + aᵢ₊₂`, and then
   `aᵢ + aᵢ₊₄` is strictly between that and `aᵢ₊₂ + aᵢ₊₄`, where either chain value would
   complete a three-term progression. These extra sums increase with `i`, so `A` has at least
   `3t - 7` pairwise sums. All of them are even, their halves lie in `[0,n)` and are not in `S`
   (they would be midpoints of a progression), so `k + 3t - 7 ≤ n`, i.e. `k + 3⌈k/2⌉ ≤ n + 7`,
   whose largest solution is `moser n`.

The proof strategy for (1) and the pointer to (2) and (3) came from a consultation with a
second model (see Setup); the enumeration of small extremal sets that guided the case
analyses was done with a short Python script outside Lean.

## How the proofs were obtained

Written by hand with the AI agent named below, checked with `lake env lean` on scratch files
before assembly. `valid` is `patch_valid'` over `minWith_valid`; `improves` is
`minWith_improves` followed by `patch_improves'` (`8 ≤ 9` at `n = 17`, by `decide`); `strict`
is the witness `n₀ = 100` (`51 → 42`) by `decide`.

The only delicate part was Moser's count, done in index form (`moser_index`): an enumeration
`a : ℕ → ℕ` that is strictly increasing on `[0, t)`, a `chain` finset, and an `extra` function
choosing the sum outside the chain. Every inequality reduces to instances of monotonicity
handed to `omega`; the interleaving of the chain is proved by `card_image_of_injOn` and a
disjointness argument. Nothing here evaluates `rothNumberNat`.

The whole file costs about 55000 heartbeats (`lake exe squeeze budget-probe`), the heaviest
declaration being `roth12`.

## Setup

- Tools: Claude Code with the model Claude Fable 5.1 (`claude-fable-5-1`) as the agent, one
  consultation of GPT-6 Astra via the `askgpt` tool for literature and proof strategy, Lean 4
  (v4.31.0) with the pinned Mathlib, Python 3.12 for enumerating small 3-AP-free sets.
- Machine: 96 cores, 755 GB RAM (32 GB budget for this job), Linux 6.8.0-124-generic.
- Time: about three hours from reading the track to acceptance. No search ran inside Lean.
