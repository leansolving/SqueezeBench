# Roth numbers `r₃(n)`

`f(n)` is the largest size of a subset of `{0, …, n-1}` containing no three-term arithmetic
progression.

The growth rate is the subject of Roth's theorem and its descendants. Behrend's construction
gives `n · exp(−c√(log n))` from below; the best upper bound is Bloom–Sisask's
`n / (log n)^{1+c}`. The gap between them is open.

`nMin = 1`.

## Known values

**Reporting only. These are never a source of theorems** — except that
here, unusually, the first four *are* theorems: `f` is computable, so `Def.lean` checks them
with `decide` on every build.

| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| f(n) | 1 | 2 | 2 | 3 | 4 | 4 | 4 | 4 | 5 | 5 | 6 | 6 | 7 | 8 |

Citation: OEIS [A003002](https://oeis.org/A003002), which tabulates far further. The kernel
cost of `decide` grows as `2ⁿ`, so `n = 4` is the practical limit for checking; the rest are
cited. Note the long plateaus — `f` is constant on `5..8` — which is why the transition count
rather than the term count measures this problem's ground truth.

## Formalisation status

`f` is `rothNumberNat`, pinned below `nMin`. **Nothing is redefined**: Mathlib's
`rothNumberNat n = addRothNumber (Finset.range n)` already *is* this quantity, a
`Nat.findGreatest` over the `ThreeAPFree` subsets of `range n`.

- **Total by construction** — the supremum is over a `Fintype` and the empty set qualifies, so
  there is no `Finite.lean` and no well-posedness obligation.
- **Computable**, unusually for this suite. That is what lets the known values be checked.
- Transfer lemmas: `le_f_of_threeAPFree` (exhibit a 3-AP-free set) and `f_le_self`. `f_mono`
  carries a bound proved at one `n` to every larger one.

## Seeded records

| direction | record | `n=1` | `n=2` | `n=3` | `n=5` |
|---|---|---|---|---|---|
| lower | `pin nMin (min n 2)` | **1** | **2** | 2 | 2 |
| upper | `n` | **1** | **2** | 3 | 5 |

True values: `1, 2, 2, 4`.

**The two records meet at `n = 1` and `n = 2`.** `lower = upper` there, so the conjunction of
`Lower.V000.valid` and `Upper.V000.valid` proves `r₃(1) = 1` and `r₃(2) = 2` outright, with no
citation in the chain. The lower record is also exact at `n = 3`.

Neither seed needed a witness construction: the lower record follows from `f 1 = 1` and
`f 2 = 2` — both settled by the kernel — plus monotonicity.

## Where the next improvement lies

**Both sides are wide open, and the lower side is the interesting one.**

The lower record is constant at `2`, against a truth that grows almost linearly. The classical
next step is the Szekeres construction — the integers below `3ᵏ` whose base-3 digits avoid `2`
— giving `2^k ≈ n^{log 2 / log 3} ≈ n^{0.63}`. Beyond that is Behrend.

> **Behrend cannot be a record as it stands.** `Behrend.roth_lower_bound` is stated over `ℝ`
> and involves `Real.exp` and `Real.log`, which are noncomputable, while a record must be
> computable (gate 4). Using it means first exhibiting a computable ℕ-valued function below it
> — a rational approximation — and that conversion, not the mathematics, is the work. The same
> obstacle applies to Ruzsa–Szemerédi, whose Mathlib lower bound routes through this one.

On the upper side, `n` is the trivial bound; anything better is Roth's theorem or a finite-`n`
argument, and Bloom–Sisask is far out of reach of formalisation today.

## Current state

| | |
|---|---|
| Well posed | **yes** — total by construction |
| Lower record | `Records/Lower/V009/` — beats V008 at witness `8000` (trial claude-fable; based on V001, V002, V004, V005, V006, V007, V008, 2026-09-25) |
| Upper record | `Records/Upper/V007/` — beats V006 at witness `100` (trial claude-fable; based on V002, V003, V004, V005, V006, 2026-09-25) |
| Live | **yes** — both Challenges open at `V001`; `squeeze audit Roth` accepts both seeds |

## Record history

One row per accepted version, oldest first, appended by `lake exe squeeze accept`.
The author is the `name` in the record's `metadata.toml`.

### Upper

| version | date | author | witness | value at the witness |
|---|---|---|---|---|
| V001 | 2026-09-24 | baseline claude-opus-5 | 3 | 3 → 2 |
| V002 | 2026-09-24 | baseline claude-opus-5; based on V001 | 8 | 6 → 5 |
| V003 | 2026-09-24 | baseline claude-opus-5; based on V001, V002 | 7 | 5 → 4 |
| V004 | 2026-09-24 | baseline claude-opus-5; based on V001, V002, V003 | 8 | 5 → 4 |
| V005 | 2026-09-25 | trial claude-fable; based on V002, V003, V004 | 100 | 51 → 42 |
| V006 | 2026-09-25 | trial claude-fable; based on V002, V003, V004, V005 | 1000 | 402 → 366 |
| V007 | 2026-09-25 | trial claude-fable; based on V002, V003, V004, V005, V006 | 100 | 40 → 39 |

### Lower

| version | date | author | witness | value at the witness |
|---|---|---|---|---|
| V001 | 2026-09-24 | baseline claude-opus-5 | 9 | 2 → 4 |
| V002 | 2026-09-24 | baseline claude-opus-5; based on V001 | 14 | 4 → 8 |
| V003 | 2026-09-24 | baseline claude-opus-5; based on V001, V002 | 9 | 4 → 5 |
| V004 | 2026-09-24 | baseline claude-opus-5; based on V001, V002, V003 | 24 | 8 → 10 |
| V005 | 2026-09-24 | baseline claude-opus-5; based on V001, V002, V003, V004 | 28 | 10 → 11 |
| V006 | 2026-09-24 | baseline claude-opus-5; based on V001, V002, V003, V004, V005 | 33 | 12 → 13 |
| V007 | 2026-09-25 | trial claude-fable; based on V001, V002, V003, V004, V005, V006 | 209 | 38 → 43 |
| V008 | 2026-09-25 | trial claude-fable; based on V001, V002, V005, V006, V007 | 2187 | 176 → 190 |
| V009 | 2026-09-25 | trial claude-fable; based on V001, V002, V004, V005, V006, V007, V008 | 8000 | 430 → 448 |
