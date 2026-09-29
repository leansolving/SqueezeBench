# Roth, lower bound — submission report

Track: `Roth` / lower. `f n = r₃(n)` is the largest size of a 3-AP-free subset of `{0, …, n-1}`
(Mathlib's `rothNumberNat`, pinned to `0` below `nMin = 1`). Submitter: `baseline claude-opus-5`.

## What the literature gives

- **Exact small values** — OEIS [A003002](https://oeis.org/A003002):
  `r₃(n) = 1, 2, 2, 3, 4, 4, 4, 4, 5, 5, 6, 6, 7, 8, 8, 8, 8, 8, 8, 9, …` for `n = 1, 2, …`.
  Only the first four are theorems in this repository (`Def.lean` checks them by `decide`);
  the rest are reporting only.
- **Szekeres (folklore, pre-Behrend)** — the integers below `3ᵏ` whose base-3 digits avoid `2`
  are 3-AP-free, so `r₃(3ᵏ) ≥ 2ᵏ`, i.e. `r₃(n) ≳ n^{log 2 / log 3} = n^{0.6309…}`. It is the
  construction Erdős and Turán note as the naive one in *On some sequences of integers*,
  J. London Math. Soc. 11 (1936), 261–264.
- **Behrend (1946)** — `r₃(n) ≥ n · exp(−c √(log n))`, *On sets of integers which contain no
  three terms in arithmetical progression*, PNAS 32, 331–332. In Mathlib as
  `Behrend.roth_lower_bound : (N : ℝ) * exp (-4 * √(log N)) ≤ rothNumberNat N`, with the
  usable discrete form `Behrend.bound_aux' : (d ^ n / (n * d ^ 2) : ℝ) ≤ rothNumberNat ((2d-1) ^ n)`.
- **Elkin (2011), Green–Wolf (2010)** — improve Behrend by a factor `√(log n)`.
- Upper side (not this track): Bloom–Sisask, `r₃(n) ≤ n / (log n)^{1+c}`.

Behrend beats Szekeres only around `n ≈ e^{117}`, and the `1/(n d²)` loss in `bound_aux'`
pushes the crossover further still, so at every `n` a reviewer will look at, the base-3 digit
construction is the better bound. That is what all three versions below use.

## V001 — `baseline claude-opus-5`

**Bound.** `record = max(min n 2, 2 ^ ⌊log₃ n⌋)` for `n ≥ 1` (`maxWith` over the V000 seed).

**Idea.** Tripling: if `A ⊆ [0, m)` is 3-AP-free then `3A ∪ (3A + 1) ⊆ [0, 3m)` is 3-AP-free
and twice as large, so `f (3m) ≥ 2 f m`. A three-term progression `x + z = 2y` in the new set
has `x ≡ y ≡ z (mod 3)` — the last base-3 digits lie in `{0,1}`, so `x%3 + z%3 = 2·(y%3)`
forces them equal (`omega`) — and dividing by `3` lands back in `A`. Iterating from `f n ≥ 1`
gives `2 ^ ⌊log₃ n⌋`, computed by `szAux`, a structural recursion on a fuel argument so the
kernel can evaluate it in `O(log n)` steps (`Nat.log` is well-founded and does **not** reduce
in the kernel — that would have failed gate 6).

**Why.** It is the classical next step named in the problem README, it improves at every
`n ≥ 3`, and it gives a growth rate `n^{0.63}` against the seed's constant `2`.

**Witness.** `n₀ = 9`: `2 → 4`.

## V002 — `baseline claude-opus-5` (based on V001)

**Bound.** `record = max(V001, c n)` where `c n` is the **exact** number of integers in
`[0, n)` whose base-3 digits avoid `2`:

    c n = n                               (n ≤ 2)
    c n = c ⌈n/3⌉ + c ⌈(n-1)/3⌉           (n ≥ 3)

**Idea.** The same digit argument, but splitting on the last digit at an arbitrary bound
instead of only at powers of `3`: with `A ⊆ [0, ⌈n/3⌉)` and `B ⊆ [0, ⌈(n-1)/3⌉)` maximal
3-AP-free sets, `3A ∪ (3B + 1) ⊆ [0, n)` is 3-AP-free, so
`f n ≥ f ⌈n/3⌉ + f ⌈(n-1)/3⌉`. A progression in the union has all three last digits equal,
hence lies entirely in `3A` or entirely in `3B + 1`, which is why the two halves may be
different sets. `cntAux` is again fuel-structural; its recursion depth is `log₃ n`.

**Why.** It removes the staircase of V001 — `2 ^ ⌊log₃ n⌋` is tight only at `n = 3ᵏ` — and
is exact (`= f n`) at `n = 1,2,3,4,5,6,7,8,10,11,12,13,14,15`, i.e. it matches the true Roth
number at every `n ≤ 15` except `n = 9`.

**Witness.** `n₀ = 14`: `4 → 8`.

## V003 — `baseline claude-opus-5` (based on V001, V002)

**Bound.** `record = max(V002, c' n)`, where `c'` is the V002 recursion with a better base
case:

    c' n = c n                              (n ≤ 8)
    c' 9 = 5
    c' n = c' ⌈n/3⌉ + c' ⌈(n-1)/3⌉          (n ≥ 10)

**Idea.** `n = 9` is the first place the base-3 digit set is not optimal: it gives
`{0,1,3,4}`, but `{0,1,3,7,8} ⊆ [0,9)` is 3-AP-free too, so `f 9 ≥ 5`. The last-digit
recursion of V002 is multiplicative in its base values, so this one extra point lifts the
bound by `5/4` wherever `9` appears in the recursion tree — `c' 27 = 10` against `c 27 = 8`,
`c' 81 = 20` against `16`, and so on along every `3ᵏ`.

**Why.** It is a strict improvement at infinitely many `n` (all `n = 3ᵏ`, `k ≥ 2`, and every
`n` whose splitting tree reaches `9`) for a single small certified construction; it does not
improve every `n` — e.g. `c' 1000 = c 1000 = 105`, because the tree of `1000` bottoms out at
`13` without passing through `9`.

**Witness.** `n₀ = 9`: `4 → 5`.

## Values

| n | 1 | 2 | 3 | 4 | 5 | 9 | 10 | 14 | 20 | 27 | 81 | 243 | 1000 |
|---|---|---|---|---|---|---|----|----|----|----|----|-----|------|
| V000 (start) | 1 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 |
| V001 | 1 | 2 | 2 | 2 | 2 | 4 | 4 | 4 | 4 | 8 | 16 | 32 | 64 |
| V002 | 1 | 2 | 2 | 3 | 4 | 4 | 5 | 8 | 8 | 8 | 16 | 32 | 105 |
| V003 | 1 | 2 | 2 | 3 | 4 | 5 | 5 | 8 | 8 | 10 | 20 | 40 | 105 |
| true `f n` (A003002) | 1 | 2 | 2 | 3 | 4 | 5 | 5 | 8 | 9 | 11 | ? | ? | ? |

## What the next improvement would take

1. **A better base case.** Certifying exact values by explicit sets and using
   them as the base of the recursion multiplies the bound wherever they appear in the splitting tree. V003 did
   this for `f 9 ≥ 5`; `f 20 ≥ 9` and `f 26 ≥ 11` are the next two, and a base table covering
   all `n ≤ 26` would lift the bound by `11/8` along the powers of `3`. Each entry costs one
   explicit set and one `omega` over its triples — the cheapest genuine gain left.
2. **A better digit alphabet.** The split lemma generalises: for any base `q` and any
   `D ⊆ [0, q)` that is 3-AP-free *in `ℤ/q`*, `f n ≥ Σ_{d ∈ D} f ⌈(n-d)/q⌉`. The exponent
   becomes `log |D| / log q`, so any `(q, D)` beating `log 2 / log 3` improves the bound at
   infinitely many `n`. The Lean cost is a `|D|`-fold union instead of a two-fold one, and the
   kernel cost of the record grows to `n^{log|D|/log q}` branches.
3. **Behrend.** `Behrend.bound_aux'` is usable as stated (it is about `rothNumberNat`, and the
   record itself may stay ℕ-valued: pick `d`, `n` and bound `d^n / (n d²)` from below in ℕ).
   Worth folding in with `maxWith` for the asymptotics, but it loses to the digit construction
   at every `n` below roughly `e^{117}`, so it would change no visible value.

**Problems hit.** Two, both about kernel evaluation rather than mathematics: `Nat.log` and any
other well-founded definition is unusable inside a record (the kernel cannot unfold
`WellFounded.fix`), so every recursion here is structural in an explicit fuel argument; and the
branching form of `c n` costs `n^{0.63}` kernel steps, which is why the witnesses are small.

## V004 — `baseline claude-opus-5` (based on V001, V002, V003)

**Bound.** `record = max(V003, c₄)` where `c₄` is the last-digit recursion with the **whole
window `n ≤ 27`** as base case:

    c₄ n = tbl n                             (n ≤ 27)
    c₄ n = c₄ ⌈n/3⌉ + c₄ ⌈(n-1)/3⌉           (n ≥ 28)
    tbl n = max (#{x ∈ A : x < n}) (#{x ∈ B : x < n}) (V003.cnt n)

with two explicit 3-AP-free sets `A = {0,1,4,6,10,15,17,18,22,23,25} ⊆ [0,26)` and
`B = {0,1,5,6,8,13,14,17,19} ⊆ [0,20)`, found by a local search (insertion with repair).

**Idea.** Every *prefix* of a 3-AP-free set is a 3-AP-free subset of `[0, n)`, so one set
certifies a whole row of the base table at once — `|A ∩ [0,n)|` gives `f 23 ≥ 9`, `f 24 ≥ 10`,
`f 26 ≥ 11`, and `B` gives `f 20 ≥ 9`. The table therefore carries the true Roth number
(A003002) at every `n ≤ 27`, where V003's recursion was short by up to `2` (`c′ 24 = 8`,
`f 24 = 10`). The recursion is multiplicative in its base, so the gain propagates:
`f 81 ≥ 22` against V003's `20`, `f 243 ≥ 44` against `40`.

**Why.** It is improvement 1 of the V003 notes — a better base — carried out for the whole
window rather than a single point, and the prefix trick makes it two certificates instead of
nineteen. It improves at infinitely many `n`: every `n` whose splitting tree reaches `20 … 27`.

**Witness.** `n₀ = 24`: `8 → 10`.

**Cost.** `ThreeAPFree` is certified by one `decide` over the `|A|³ = 1331` triples
(`a + c ≠ b + b ∨ a = c`), lifted by `free_of_all`; 3211 heartbeats for the larger set, 7758
for the whole file. A cubic `decide` over a list is far below the budget, so much larger base
sets are affordable.

## V005 — `baseline claude-opus-5` (based on V001, V002, V003, V004)

**Bound.** `record = max(V004, c₅)` with

    c₅ n = tbl n                                          (n ≤ 27)
    c₅ n = max (tbl 27) (c₅ ⌈n/3⌉ + c₅ ⌈(n-1)/3⌉)         (n ≥ 28)

**Idea.** `f` is monotone but the recursion is not: it drops from `c₄ 27 = 11` to `c₄ 28 = 10`,
and repeats the dip just above every power of `3` — `c₄ 82 = 21` against `c₄ 81 = 22`,
`c₄ 244 = 43` against `c₄ 243 = 44`. Feeding `f n ≥ f 27 ≥ 11` (`f_mono`) into every level of
the recursion removes all of them at once: with a monotone base table the recursion becomes
monotone, because `n ↦ ⌈n/3⌉` is.

**Why.** A defect of the shape of the record rather than of the mathematics, costing up to
`1` in `11` at infinitely many `n`, repaired by one `le_trans`.

**Witness.** `n₀ = 28`: `10 → 11`.

## Values (V003 → V005)

| n | 9 | 20 | 24 | 26 | 27 | 28 | 40 | 81 | 82 | 243 | 244 | 1000 |
|---|---|----|----|----|----|----|----|----|----|-----|-----|------|
| V003 | 5 | 8 | 8 | 10 | 10 | 10 | 15 | 20 | 20 | 40 | 40 | 105 |
| V004 | 5 | 9 | 10 | 11 | 11 | 10 | 15 | 22 | 21 | 44 | 43 | 105 |
| V005 | 5 | 9 | 10 | 11 | 11 | 11 | 15 | 22 | 22 | 44 | 44 | 105 |
| true `f n` (A003002) | 5 | 9 | 10 | 11 | 11 | 11 | ? | ? | ? | ? | ? | ? |

## What the next improvement would take (after V005)

1. **A wider base window.** The same prefix trick at `N = 40`, `54` or `81` multiplies the
   bound again, but it needs 3-AP-free sets that beat the recursion there — `c₅ 40 = 15`,
   `c₅ 54 = 16`, `c₅ 81 = 22`. The insertion-with-repair search used here does **not** reach
   them: seeded with the recursive set it never improved on it for `N ≥ 40`, and unseeded it
   stays well below (`13` at `N = 40`, `20` at `N = 81`). An exact solver — branch and bound,
   or a SAT/ILP model of the `≈ N²/2` progressions — is the next tool to bring. The Lean side
   is already cheap: the cubic `decide` for a 25-element set is about `40000` heartbeats, still
   inside the budget, and the base table costs one certificate per set however wide the window.
2. **Mid-window values.** `tbl` is exact on `n ≤ 27`, so nothing is left below the window; all
   remaining gains are at `n ≥ 28`.
3. **A better digit alphabet** (V003 notes, item 2) — still open, and still the only route to
   an exponent above `log 2 / log 3`. Every small modulus checked by hand (`q ≤ 9`) has a
   cyclic 3-AP-free set of size at most `q^{log 2 / log 3}`, so the modulus has to be large
   enough for a Behrend-type set in `ℤ/q`, which is a substantial construction.
4. **Behrend** — unchanged: usable via `Behrend.bound_aux'`, visible only near `n ≈ e^{117}`.

**Problems hit (V004–V005).** None in Lean: the budget was never close (7758 and 1911
heartbeats). The bottleneck was the search for large 3-AP-free sets — the heuristic matches
the known optimum up to `n ≈ 27` but falls behind the recursive construction beyond it.

## V006 — `baseline claude-opus-5` (based on V001, V002, V003, V004, V005)

**Bound.** `record = max(V005, c₆)` where the base window of the last-digit recursion is widened
from `n ≤ 27` to `n ≤ 56`:

    c₆ n = tbl₆ n                                          (n ≤ 56)
    c₆ n = max (tbl₆ 56) (c₆ ⌈n/3⌉ + c₆ ⌈(n-1)/3⌉)         (n ≥ 57)
    tbl₆ n = max (#{x ∈ C : x < n}) (#{x ∈ D : x < n}) (V005.cnt n)

with two new explicit 3-AP-free sets

    C = {1,2,5,7,10,11,14,22,24,25,29,31,32} ⊆ [0,33)      (|C| = 13)
    D = {2,3,5,6,12,13,15,16,31,36,38,39,43,44,51,53,54} ⊆ [0,55)   (|D| = 17)

**Idea.** Item 1 of the V005 notes, carried out with a stronger search. Instead of the
insertion-with-repair heuristic (which stalls above `n ≈ 27`), this is a fixed-size WalkSAT-style
local search: fix a target size `k = c₅(n) + 1`, start from a random `k`-subset of `[0, n)`, and
repeatedly swap out an element that takes part in a progression for the best replacement. It
found a 3-AP-free 13-set in `[0,33)` where the recursion gives only `12`, and a 17-set in
`[0,55)` where the recursion gives `16`. The prefix trick of V004 then fills the whole window
`28 … 56` from these two certificates, and the recursion above `56` is multiplicative in its
base, so the gain propagates to infinitely many `n` — e.g. `c₆ 100 = 26` against `c₅ 100 = 24`,
`c₆ 163 = 33` against `32`.

**Where it improves inside the window.** `n = 33 … 36` (`12 → 13`) and `n = 55, 56` (`16 → 17`);
elsewhere in `n ≤ 56` the V005 recursion was already equal to the best set found, which is
evidence it is exact there.

**Witness.** `n₀ = 33`: `12 → 13`.

**Cost.** 18391 heartbeats for the whole file (limit 200000), the bulk being the two cubic
`decide`s certifying `ThreeAPFree`: 11186 for the 17-element set, 5160 for the 13-element set.
A 17³ = 4913-triple check is still an order of magnitude inside the budget, so sets of size
~30 remain affordable.

## Values (V005 → V006)

| n | 33 | 36 | 40 | 55 | 56 | 81 | 100 | 163 | 1000 |
|---|----|----|----|----|----|----|-----|-----|------|
| V005 | 12 | 12 | 15 | 16 | 16 | 22 | 24 | 32 | 105 |
| V006 | 13 | 13 | 15 | 17 | 17 | 22 | 26 | 33 | 105 |
| true `f n` (A003002) | 13 | 13 | 15 | ? | ? | ? | ? | ? | ? |

## What the next improvement would take (after V006)

1. **Widen the window again.** The same WalkSAT search at `N = 81, 108, 163` is the direct
   continuation; each new certificate lifts the whole tree above it. The search cost grows
   quickly — at `N = 28, 40, 46` it failed to beat the recursion within the time given, which
   suggests those are already exact, but `N ≥ 57` was not attempted for lack of time and is the
   obvious place to look next. The Lean side is cheap and unchanged: one list, one `decide`,
   one row of `tbl`.
2. **A stronger solver.** The local search is incomplete: a failure to find size `k` is not a
   proof that `r₃(N) < k`. An exact branch-and-bound or a SAT/ILP model over the `≈ N²/2`
   progressions would both find more and tell us where the recursion is already optimal.
3. **A better digit alphabet / Behrend** — unchanged from the V003 and V005 notes; still the
   only routes to an exponent above `log 2 / log 3`, and still out of reach of a short session.

**Problems hit (V006).** None in Lean. The binding constraint remains the combinatorial search.

## Session note — `baseline claude-opus-5`, continuation after V006

No version was accepted in this session; the record stands at **V006**.

**What was attempted.** Item 1 of the V006 notes — widen the base window past `n ≤ 56`. The
targets are exactly the places where the last-digit recursion `c₆` sits, so a new certificate
must beat:

| n | 57 | 60 | 70 | 81 | 90 | 100 | 120 | 163 | 243 |
|---|----|----|----|----|-----|-----|-----|-----|-----|
| `c₆ n` | 17 | 18 | 19 | 22 | 22 | 26 | 30 | 33 | 44 |

**Result.** A fixed-size WalkSAT-style local search (random `k`-subset of `[0, N)`; repeatedly
evict a vertex of a 3-AP and reinsert the candidate minimising the number of progressions,
with a 30 % random-walk step) was run at `(N, k) = (60, 19)`, `(70, 20)`, `(81, 23)`,
`(100, 27)` and `(120, 31)`. **None succeeded** within the time given (tens of seconds each).
This is weak evidence that `c₆` is at or near the truth in the range `57 … 120`, but the search
is incomplete, so it is not a proof — the same heuristic did find the V006 certificates at
`N = 33, 55` only after many restarts, and the search space grows as `C(N, k)`.

**Conclusion for the next submitter.** The cheap gains from widening the base window appear to
be exhausted at this search strength. The two routes left are unchanged and both are real work:

1. **An exact solver.** A SAT or ILP model over the `≈ N²/2` progressions in `[0, N)`, or a
   branch-and-bound with the recursion value as an incumbent, would either produce a
   certificate at `N = 81 … 120` or show that `c₆` is already optimal there. This is the
   highest-value next step: it converts guesswork into a decision. The Lean side is already
   mechanical — one list, one cubic `decide` (a 25-element set costs about `40000`
   heartbeats against the `200000` budget), one row of `tbl`, and the existing `below_le` /
   `free_of_all` plumbing from V004 carries it.
2. **A better digit alphabet**, `f n ≥ Σ_{d ∈ D} f ⌈(n-d)/q⌉` for `D` 3-AP-free in `ℤ/q`, which
   is the only route to an exponent above `log 2 / log 3`. Every modulus small enough to check
   by hand loses: the largest 3-AP-free set in `ℤ/9` is `{0,1,3,4}` of size `4 = 9^{log 2/log 3}`,
   so the exponent is unchanged. A gain needs a Behrend-type set in `ℤ/q` for large `q`, which
   is a construction in its own right, and the record's kernel cost then grows as
   `n^{log|D|/log q}` branches.
3. **Behrend** — unchanged: usable through `Behrend.bound_aux'`, invisible below `n ≈ e^{117}`.

## V007 — `trial claude-fable` (based on V001–V006)

**Bound.** `record = max(V006, c₇)` where `c₇` is the last-digit recursion with the base window
widened from `n ≤ 56` to `n ≤ 209` and filled with the **exact** Roth numbers there:

    c₇ n = r₃(n)                                          (n ≤ 209, the table `tblList`)
    c₇ n = max (r₃(209)) (c₇ ⌈n/3⌉ + c₇ ⌈(n-1)/3⌉)         (n ≥ 210)

**Idea.** The exact values are known to `n = 211` (OEIS A003002: Dybizbański to `123`, Cariboni
to `211`), and the OEIS a-file of A003002 prints an extremal set for every `n = 4 … 209`. One
certificate per *jump node* of `r₃` (43 of them up to `209`, the largest of size `43` inside
`[0, 209)`) certifies the whole table, because between jump nodes the earlier set still has the
right size. So `tblList` is exact on `n ≤ 209`, where V006 was short at 118 of the `n ≤ 211`
(already at `n = 30, 31, 32, 36, 37, 51 … 57` inside its own window, and by `5` at `n = 209`).

**Certificates.** A quadratic check replaces the cubic `decide` of V004–V006: `chk l m` tests,
for every pair `a < b` of the list, that `2b - a` is not set in the bitmask `m` (`Nat.testBit`,
kernel-accelerated shift and mask). For the 32-element set this costs 716 (thousand heartbeats)
against 16642 for the cubic kernel check, so all 44 certificates cost 26336 together, and a
second `decide +kernel` (`tblOK`, 12772) links the table to the certificates: for every
`n < 210`, the first certificate whose jump node is `≤ n` has at least `tblList[n]` elements
below `n`. The whole `Proof.lean` is 52491 of the 200000 budget.

**Why.** Item 1 of the V006 notes, carried to the end of the known values with published sets
instead of a search. Strictly larger than V006 at almost every `n ≥ 30` (every `n` whose
splitting tree reaches an improved entry), and the last step the known values allow for this
recursion.

**Witness.** `n₀ = 209`: `38 → 43`.

## Values (V006 → V007)

| n | 30 | 32 | 57 | 63 | 100 | 122 | 174 | 209 | 243 | 500 | 729 | 1000 | 2187 |
|---|----|----|----|----|-----|-----|-----|-----|-----|-----|-----|------|------|
| V006 | 11 | 12 | 17 | 18 | 26 | 32 | 36 | 38 | 40 | 66 | 78 | 105 | 160 |
| V007 | 12 | 13 | 18 | 20 | 27 | 32 | 40 | 43 | 44 | 76 | 88 | 116 | 176 |
| true `f n` (A003002) | 12 | 13 | 18 | 20 | 27 | 32 | 40 | 43 | ? | ? | ? | ? | ? |

## What the next improvement would take (after V007)

The base window is exhausted: `r₃(n)` is unknown for `n ≥ 212` (`r₃(212) ∈ {43, 44}` is open,
Ergezer 2026, arXiv:2606.04016). Every further gain is above `n = 211`, from a better recursion
or from new sets.

1. **A better recursion, closed over the table.** Two more rules are valid and, seeded with the
   exact table, beat the balanced base-3 rule at infinitely many `n`:
   - *concatenation with a gap*: if `A ⊆ [0, a)` and `B ⊆ [0, b)` are 3-AP-free and
     `s ≥ max(2a - 1, a + b - 1)`, then `A ∪ (B + s)` is 3-AP-free, so
     `f (s + b) ≥ f a + f b` — an unbalanced split that exploits the staircase of `r₃`
     (`46` against `44` at `n = 243`, `92` against `88` at `729`, `184` against `176` at `2187`);
   - *a modular product*: if `D ⊆ [0, q)` has no solution of `x + z ≡ 2y (mod q)` other than
     `x = y = z`, then `⋃_{d ∈ D} (q·A_d + d)` is 3-AP-free, so `f n ≥ Σ_{d ∈ D} f ⌈(n - d)/q⌉`.
     `D = {0, 1, 4, 6, 10, 15, 17, 18, 23, 25}` works for `q = 37` (it is the block of the
     extremal set at `n = 174`, which is `D + 37·{0, 1, 3, 4}`), and `10 > 37^{log 2 / log 3}`, so
     the exponent improves to `log 10 / log 37 = 0.6377`; `80` against `78` at `n = 507`, `190`
     against `176` at `2187`, `400` against `352` at `6561`.
   Taking the closure of all rules gives `46, 80, 92, 158, 190, 400` at `n = 243, 507, 729, 1500,
   2187, 6561`. The kernel cannot afford the concatenation rule as a tree recursion (it branches
   on the split point), so the closure has to be tabulated: a Nat-encoded table of values with a
   per-entry certificate naming the rule and its parameter, checked by one `decide +kernel`, and
   the tree recursion (balanced and modular rules only) above the table.
2. **New sets above `211`.** Gasarch–Glenn–Kruskal (*Finding large 3-free sets I*, JCSS 2008,
   Table 3) report lower bounds `44` at `215`, `45` at `227`, `46` at `233`, `47` at `239`, `48` at
   `247`, one better than the closure of item 1 around there, but print only cardinalities. A
   SAT/CP search seeded with the closure's value as the target is the way to get such sets; the
   Lean side is one more certificate each.
3. **Behrend** — unchanged: usable via `Behrend.bound_aux'`, invisible below `n ≈ e^{117}`.

## V008 — `trial claude-fable` (based on V001, V002, V005, V006, V007)

**Bound.** `record = max(V007, c₈)`, with `c₈` the closure of four rules over the exact table,
tabulated for `n ≤ 3000` (a single natural number, 16 bits per entry, read by a shift and a
mask) and continued above by a tree recursion:

    c₈ n = max over the rules below, over all earlier entries                     (n ≤ 3000)
    c₈ n = max (c₈ 3000) (c₈ ⌈n/3⌉ + c₈ ⌈(n-1)/3⌉) (Σ_{d ∈ D37} c₈ ⌈(n-d)/37⌉)      (n > 3000)

The rules: (1) the V007 table for `n ≤ 209`; (2) monotonicity; (3) the balanced split of V002;
(4) *concatenation with a gap*, `f n ≥ f a + f b` for `1 ≤ a ≤ b`, `a + 2b - 1 ≤ n`; (5) the
*modular product* `f n ≥ Σ_{d ∈ D37} f ⌈(n-d)/37⌉` with `D37 = {0,1,4,6,10,15,17,18,23,25}`,
3-AP-free modulo `37` in the strong sense (`x + z ≡ 2y` only for `x = y = z`).

**Idea.** Rule 4 exploits the staircase of `r₃` with unbalanced splits, rule 5 is the digit
construction with a better alphabet (`|D37| = 10 > 37^{0.6309}`, exponent `0.6377`), taken from
the extremal set at `n = 174`, which is `D37 + 37·{0,1,3,4}`. Neither can be a cheap tree
recursion (rule 4 branches on the split point), so the closure is *tabulated*: each entry
carries a certificate naming its rule and parameter (`codes`, 16 bits per entry), one
`decide +kernel` checks all 3001 entries against their named candidates (10718 heartbeats), and
a strong induction turns the check into `get n ≤ f n`. The two rule lemmas follow the
V001/V002 union pattern; the modular one uses `Finset.biUnion` over the ten digit sets.

**Gains over V007.** `45` vs `44` at `237`, `46` vs `44` at `243`, `80` vs `78` at `507`,
`92` vs `88` at `729`, `158` vs `152` at `1500`, `190` vs `176` at `2187`, `400` vs `352` at
`6561`; larger at 1868 of the `n ≤ 3000` and at infinitely many `n` above.

**Witness.** `n₀ = 2187`: `176 → 190`.

**Cost.** 47349 heartbeats for `Proof.lean` (`cat_le` 13067, `check_eq` 10718, `get_le` 10447,
`mod37_le` 6595); the record costs about 20 at any `n ≤ 3000`.

## Values (V007 → V008)

| n | 237 | 243 | 400 | 507 | 729 | 1000 | 1500 | 2000 | 2187 | 3000 | 6561 |
|---|-----|-----|-----|-----|-----|------|------|------|------|------|------|
| V007 | 44 | 44 | 64 | 78 | 88 | 116 | 152 | 176 | 176 | 232 | 352 |
| V008 | 45 | 46 | 65 | 80 | 92 | 116 | 158 | 180 | 190 | 232 | 400 |

## V009 — `trial claude-fable` (based on V001, V002, V004–V008)

**Bound.** `record = max(V008, c₉)`: the V008 closure with (1) 88 new explicit 3-AP-free sets
at `215 ≤ n ≤ 2783` (sizes `44 … 226`), (2) two more alphabets for the modular product rule,
`D85` (17 residues mod 85) and `D65` (14 residues mod 65), and (3) the table extended to
`n ≤ 10000` (12 bits per entry); above the table the tree recursion applies the balanced split
and the three modular products.

**Idea.** *Tight concatenation.* `A ∪ (B + s)` is 3-AP-free for 3-AP-free `A ⊆ [0, a)`,
`B ⊆ [0, b)` as soon as `s` avoids four conflicts (`B + s` against `A` and against the third
terms and midpoints of `A`, and symmetrically), so the least such `s` gives a set at
`n = max(a, s + b)`, usually far below the safe `s = a + b - 1` of the V008 rule. The extremal
sets themselves have this shape (the one at `82` is the one at `31` followed by an 11-element
set shifted by `48`). Three search rounds over the 206 extremal sets of the OEIS a-file and
their winners (FFT correlation for the conflicts, four minutes in all) beat the V008 closure at
1191 values of `n ≤ 3000`; a greedy pass keeps the 88 sets that beat the closure of everything
before them. The alphabets come from a CP-SAT survey of all moduli `q ≤ 130`:
`|D85| = 17 > 85^{0.6309}` is the best ratio (`1.031`, proven optimal for its modulus).

**Certificates.** A *linear* check replaces the quadratic one of V007: with `M` the bitmask of a
set and `R` its mirror image in `[0, N)`, the third terms of the progressions through `b` are
`R` shifted by `N - 1 - 2b`, so `M &&& shift = 1 <<< b` — one shift, one mask, one comparison
per element (104 heartbeats for the 43-element set against 1270), and a linear `sorted` check
replaces `Nodup`. The sets are packed as 12-bit digits into one numeral each (a 226-element
list literal exceeds the elaborator's recursion depth, which `Proof.lean` may not raise); the
record's `REPORT.md` lists them in the clear. The modular lemma is proved once for any `(q, D)`.

**Gains over V008.** Larger at 5180 of the `n ≤ 10000`, by up to `18`; unchanged at
`507, 729, 1000, 2187, 6561`, where the closure is pinned by the product structure.

**Witness.** `n₀ = 8000`: `430 → 448`.

**Cost.** 123976 heartbeats (`check_eq` 34591 for the 10001 entries, `certOK_eq` 33009 for the
88 sets, `get_le` 26854).

## Values (V008 → V009)

| n | 215 | 249 | 299 | 600 | 2500 | 3000 | 5000 | 8000 | 10000 |
|---|-----|-----|-----|-----|------|------|------|------|-------|
| V008 | 43 | 47 | 54 | 83 | 202 | 232 | 322 | 430 | 512 |
| V009 | 44 | 48 | 56 | 84 | 207 | 234 | 326 | 448 | 512 |

## Values (V006 → V009, summary)

| n | 100 | 209 | 243 | 299 | 729 | 2187 | 3000 | 8000 | 10000 |
|---|-----|-----|-----|-----|-----|------|------|------|-------|
| V006 (start) | 26 | 38 | 40 | 51 | 78 | 160 | 216 | 388 | 480 |
| V007 | 27 | 43 | 44 | 54 | 88 | 176 | 232 | 430 | 512 |
| V008 | 27 | 43 | 46 | 54 | 92 | 190 | 232 | 430 | 512 |
| V009 | 27 | 43 | 46 | 56 | 92 | 190 | 234 | 448 | 512 |
| true `f n` (A003002) | 27 | 43 | ? | ? | ? | ? | ? | ? | ? |

(V006 values above `n = 700` are those of its recursion; they were not evaluated in Lean here.)

## Session end — `trial claude-fable`: unfinished work on V010

The session was closed by the maintainers while V010 was in preparation. **The record stands
at V009**; `Challenges/Roth/Lower/V010.lean` is open, and
`SqueezeBench/Problems/Roth/Records/Lower/V010/` holds only the untouched `squeeze new`
scaffold (four template files with `sorry`), which may be overwritten or removed.

**What V010 was going to be.** The V009 closure re-run with more explicit sets, found by two
searches that both work (files in the scratch directory `.lake/scratch/Roth-Lower/s/`, which
persists):

1. **Tabu search** (`tabu2.c`, compiled binary `tabu2`; usage `tabu2 n k seed seconds
   [initfile]`): a fixed-size set, swap moves, objective = number of progressions, incremental
   `O(n)` update per move, tabu tenure 5–14, random perturbation after 20000 idle moves. It
   reproduces the optimal sets at `n = 122, 174, 209` in under 90 s, and with 600 s runs it
   reached the Gasarch–Glenn–Kruskal values `45` at `227` and `46` at `233`, which V009 misses.
   Campaigns aimed one above the V009 value (`campaign.py`, `campaign2.py`, `campaign3.py`, outputs
   `campaign*.out`): with 120 s per target it succeeded at 70 of 147 targets in `212 … 358`
   (first `229`), at 4 of 100 in `421 … 520` (`457` among them), and the 600 s pass on the
   earlier failures and on "+2" targets had found `1` of `17` when stopped. The explicit sets
   found by the long runs are in `tabu_long.json` and `tabu_c3.json`; the (n, k) pairs the 120 s
   campaigns solved are listed in `tabu_session_end.json`, but their sets were not saved (the
   campaign scripts only write their JSON at the end) — rerun `tabu2 n k 1 120` (or seed `2`) to
   recover each in about the same time.
2. **Tight concatenation, round four** (`tight4.py`, output `tight4.json`): the pool of V009
   enlarged by the mirror images of every set and by the V009 certificates; 177 values of
   `n ≤ 3000` beat V009 (first `228`, e.g. `45` at `228`, `49` at `264`, `52` at `283`).

A dry run of the V010 generator (`gen10.py`, which merges `tight3.json`, `tight4.json` and every
`tabu_*.json`, re-runs the greedy selection over the V009 table as base rule, and writes
`tab10.txt`, `codes10.txt`, `sel10final.json`) with the results available at that moment gave
45 new certificates (5894 elements, largest 227), improving V009 at 1453 of the `n ≤ 10000`, by
up to `3`: `45` at `227`, `46` at `233`, `46` at `239`, `92` vs `90` at `698`, `93` vs `92` at
`729`, `117` vs `116` at `1000`, `460` vs `459` at `8610`. The Lean side is ready: `Def10.tmpl`
and `Proof10.tmpl` are complete templates (placeholders `@@TAB@@`, `@@CODES@@`, `@@CERTS@@`,
`@@WIT@@`, `@@NCERTS@@`, `@@NLO@@`, `@@NHI@@`) that reuse every V009 lemma by name (`chk2`,
`free_of_chk2`, `sorted_nodup`, `setOf`, `getD_mem_or`, `modular_le`, `mod37_le`, `mod85_le`,
`mod65_le`, `get_le`) and take the V009 table as rule `0`; the packing of the certificates is the
V009 one (12-bit digits, see the last block of `gen9.py` / the file-writing step used for V009).
To finish: run the campaigns to completion (or accept the partial results), `python3 gen10.py`,
fill the templates as for V009, `lake build`, `budget-probe` (expect about 120000 heartbeats:
the 10001-entry check and `get_le` cost about 60000 together, the certificates about 3 per
element), `verify`, `accept`. Witness suggestion: `n₀ = 233` (`44 → 46`) or `698` (`90 → 92`).

**A modular-alphabet survey is also unfinished.** `cyc.py` (results `cyc.json`) maximised, with
CP-SAT and 30 s per modulus, a strongly 3-AP-free subset of `ℤ/q` for every `q ≤ 130`: proven
optimal up to `q = 85`, where `|D| = 17` gives the best ratio `17 / 85^{log 2 / log 3} = 1.031`
(V009 uses it); `q = 65` gives `1.005`, everything else at most `1.0`. The 150 s pass
`cyc2.py` (`cyc2.out`) for `q = 86 … 104` found nothing above `0.99` and none proven optimal
beyond `q = 90`; larger moduli were not tried. Any `(q, D)` with ratio above `1.031` would be
a new rule at the cost of one `decide` (`modular_le` is general).

## What the next improvement would take (after V009)

1. **Finish V010** as described above: the cheapest gain, at more than a thousand `n ≤ 10000`
   and infinitely many above.
2. **Longer tabu runs at `212 … 500`.** Every success below `500` propagates through the
   closure; the 600 s runs beat the 120 s ones on the GGK targets, and the search could be
   seeded with the best known set at `n` instead of a random set. Values one above V010 at
   `n ≈ 300 … 500` are probably still reachable.
3. **Sets above `3000`.** The tree recursion above the table uses only the balanced split and
   the three products; a table beyond `10000` needs a second numeral (Def.lean is limited to
   64 KB; 12-bit entries reach `n ≈ 15000` in one), or 8-bit deltas.
4. **The 200000-heartbeat budget** is the binding constraint on how many explicit sets a
   version can carry: about 3 heartbeats per element with the linear check, plus about 3.5 per
   table entry for the closure check. A version that only adds certificates should reuse the
   previous table as rule `0` (as `Proof10.tmpl` does) so the check stays at one lookup per
   unchanged entry.

**Problems hit.** A 226-element list literal exceeds the elaborator's recursion depth, which
`Proof.lean` may not raise — the sets are packed into numerals instead. `List.Nodup` by
`decide` costs more than the 3-AP check itself, hence the linear `sorted`. The tabu campaigns
only save their sets at the end, which cost the 120 s results when the session was stopped.
