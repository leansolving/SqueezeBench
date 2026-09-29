# Schur — lower bound — report

Track: `SqueezeBench/Problems/Schur/Records/Lower/`. Submitter of the versions below:
`baseline claude-opus-5`.

`f k = S(k)` is the largest `N` such that `{1, …, N}` splits into `k` sum-free parts
(OEIS A045652; `x = y` is *not* allowed, so `2x = z` is forbidden too).

## What the literature gives

Exact values (reporting only — `docs/DESIGN.md` §2.2 forbids using them as theorems):

| k | S(k) | source |
|---|---|---|
| 1 | 1 | trivial |
| 2 | 4 | exhaustive |
| 3 | 13 | exhaustive |
| 4 | 44 | Golomb & Baumert, *Backtrack Programming*, JACM 12:4 (1965) 516–524 |
| 5 | 160 | M. Heule, *Schur Number Five*, AAAI-18 (arXiv:1711.08076), DRAT-verified |

Best known lower bounds beyond that:

* `S(6) ≥ 536`, `S(7) ≥ 1680` — H. Fredricksen & M. M. Sweet, *Symmetric sum-free
  partitions and lower bounds for Schur numbers*, Electron. J. Combin. 7 (2000), #R32.
  Their method is exactly the one used below: a partition of `ℤ_{2N+1} \ {0}` into `k`
  **symmetric** (`S = −S`) sum-free sets gives a sum-free `k`-partition of `[1, N]`.
* G. Exoo, *A lower bound for Schur numbers and multicolor Ramsey numbers of K₃*,
  Electron. J. Combin. 1 (1994), #R8.

Two general recurrences drive every known asymptotic lower bound. Writing `h(k) = 2·S(k) + 1`:

* **tripling** `S(k+1) ≥ 3·S(k) + 1`, i.e. `h(k+1) ≥ 3·h(k)` — one fresh colour on the
  middle third;
* **Abbott–Moser** (1966) `S(m+n) ≥ 2·S(m)·S(n) + S(m) + S(n)`, i.e. `h(m+n) ≥ h(m)·h(n)`.

So any known value `S(m)` gives `S(k) ≥ c·h(m)^{k/m}`, and the best known asymptotic base is
`h(7)^{1/7} ≥ 3361^{1/7} ≈ 3.19`. Tripling alone from a known `S(m)` only gives base `3` with
a better constant.

## Starting point

`V000` (the seed) is `S(k) ≥ (3^k − 1)/2`: the tripling tower started from the empty
colouring, `h(k) ≥ 3^k`.

## V001 — `baseline claude-opus-5`

**Bound.** `record = maxWith V000.record v` with

```
v k = 0                          for k < 4
v k = (89·3^(k−4) − 1)/2         for k ≥ 4
```

i.e. `h(k) ≥ 89·3^{k−4}` for `k ≥ 4`, against the seed's `h(k) ≥ 81·3^{k−4}`.
An improvement at **every** `k ≥ 4`, by the constant factor `89/81 ≈ 1.099`.

**Idea.** The seed hard-wires the tripling construction into a single recursive colouring
that starts from the empty one, so the tower cannot be re-based. V001 splits it:

* `SumFreeCol k M c` — "the `k`-colouring `c` has no monochromatic `x + y = z` inside `[1, M]`";
* `le_f_of_col : SumFreeCol k M c → M ≤ f k` (via `Schur.le_f`, well-posedness from `Finite.lean`);
* `ext_sumFree : SumFreeCol k M c → SumFreeCol (k+1) (3M+1) (ext c M k)` — the tripling step,
  `[1,M]` keeps its colours, `[M+1, 2M+1]` takes the fresh colour `k`, `[2M+2, 3M+1]` repeats
  `[1,M]` translated by `2M+1` (the seed's proof, generalised over an arbitrary base colouring);
* `exists_col_grow` — iterate it `j` times, reaching `G M j = ((2M+1)·3^j − 1)/2`.

The tower is then started at an **explicit optimal sum-free 4-colouring of `[1, 44]`** rather
than at nothing, which is where the `89 = 2·44 + 1` comes from. The colouring is packed base 4
into a single 26-digit numeral, `col4 n = C / 4^n % 4`; `Nat` division, `mod` and `pow` are
GMP-accelerated in the kernel, so the whole sum-freeness table is one `decide +kernel` costing
2885 heartbeats. The colouring was found by a backtracking search run outside Lean; Lean only
*checks* the construction, which is what the computation budget allows.

Total budget used: **14096 heartbeats** of 200000 (heaviest declaration `ext_sumFree`, 6180).

**Why this one.** It improves at infinitely many `k` (all `k ≥ 4`), it needs no new
mathematics beyond re-basing the seed's own construction, and the `SumFreeCol` /
`ext_sumFree` / `exists_col_grow` scaffolding is exactly what any later re-basing at a larger
known value (`S(5) ≥ 160`, `S(6) ≥ 536`) needs — such a version only has to supply a new
base colouring and change `44` to the new `M`.

**Witness.** `n₀ = 4`: `V000.record 4 = 40 < 44 = record 4`.

## Where the bound stands

| k | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
| V000 (seed) | 1 | 4 | 13 | 40 | 121 | 364 | 1093 | 3280 |
| **V001** | 1 | 4 | 13 | **44** | **133** | **400** | **1201** | **3604** |
| true `S(k)` | 1 | 4 | 13 | 44 | 160 | ≥536 | ≥1680 | — |

## What the next improvement would take

Two independent directions, in increasing order of work:

1. **Re-base the tower higher.** Supply a sum-free 5-colouring of `[1, 160]` (or any
   `M ≥ 134`) and V001's `exists_col_grow` immediately gives `h(k) ≥ (2M+1)·3^{k−5}`; with
   `M = 160` that is `321·3^{k−5}`, a factor `321/267 ≈ 1.20` over V001 at every `k ≥ 5`.
   The Lean side is nearly free — `col4_check` at `N = 44` cost 2885 heartbeats, and the
   cost grows like `N²`, so `N = 160` should land near 40000, still well inside the budget;
   `N = 536` (a 6-colouring) would be around 500000 and does **not** fit, so a re-base at
   `S(6) ≥ 536` needs the table split differently or a structural argument.
   The bottleneck is *finding* the colouring, and this is where the session ran out. What
   was tried, so the next submitter does not repeat it:
   * plain depth-first backtracking over `1, 2, …` with first-fit colour order and
     symmetry breaking on the first use of each colour reaches only depth **39**;
   * the same with randomised colour order and restarts (C, ~3·10⁸ nodes) reaches depth
     **94** — still short of the `134` needed to beat V001 at `k = 5`;
   * **the symmetric route does not exist for this `P`.** Fredricksen & Sweet search for a
     partition of `ℤ_{2N+1} \ {0}` into `k` symmetric (`S = −S`) sum-free classes. For
     `N = 160` that is `ℤ_321`, and `321 = 3·107`: the element `107` satisfies
     `107 + 107 = 214 ≡ −107`, so if `107 ∈ S` then `−107 ∈ S` and `S` is not sum-free.
     No symmetric sum-free partition of `ℤ_321` exists at all — a DFS confirms it stalls at
     depth 40. So `S(5) ≥ 160` has to be reached by a non-symmetric colouring, and finding
     one needs a real solver (SAT / local search), not naive backtracking.

   Note also that the classical "`A ∪ (−A)` is sum-free in `ℤ_{2a+1}`" lemma, which several
   write-ups state as if it were automatic, is **false**: `A = {1, 4}` is sum-free in
   `[1, 4]` but in `ℤ_9` one has `1 + 4 = 5 = −4`. Any attempt at direction 2 below must
   take the symmetry as a hypothesis, not derive it.

2. **Formalise Abbott–Moser**, `h(m+n) ≥ h(m)·h(n)`. This is the only way to beat base `3`
   (V001 already has the `SumFreeCol` / `le_f_of_col` interface it would plug into)
   asymptotically: with the `[1,44]` colouring already in the tree it would give
   `h(k) ≥ 89^{k/4}`, i.e. base `89^{1/4} ≈ 3.070` instead of `3`, and with a `[1,160]`
   colouring base `321^{1/5} ≈ 3.172`. It is a genuine piece of work: the product
   construction goes through symmetric sum-free sets in `ℤ_{2a+1}`, so one first has to
   prove that a sum-free partition of `[1, a]` yields a *symmetric* sum-free partition of
   `ℤ_{2a+1} \ {0}` — which is **not** automatic and in general needs the colouring itself
   to be symmetric. Concretely: prove `SumFreeColMod k P c` (sum-free in `ℤ_P`, `c` symmetric),
   show the base colourings found by search satisfy it, prove the product of two such is one
   for `P₁·P₂`, and re-derive `SumFreeCol` from it. That is the right target for the next
   substantial version.

### Problems hit

* `decide` cannot synthesise a `Decidable` instance for
  `∀ x < N, ∀ y < N, 1 ≤ x → 1 ≤ y → x + y ≤ M → …` (chained implications under two
  `Nat.decidableBallLT` layers), but does for
  `∀ x < N, ∀ y < N, (1 ≤ x ∧ 1 ≤ y ∧ x + y ≤ M) → …`. Use the conjunction form.
* `Nat.le_or_lt` does not exist in this toolchain; `Nat.lt_or_ge` does.

---

## Session 2 — `baseline claude-opus-5` (no new accepted version)

The record at the end of this session is still **V001**, `h(k) ≥ 89·3^{k−4}`. This session
attacked direction 1 above (re-base the tower at a sum-free 5-colouring of `[1, M]`,
`M ≥ 134`) and did not close it. What was learned is recorded here so the next submitter
does not repeat it.

### The Lean side is ready

V001's `SumFreeCol` / `ext_sumFree` / `exists_col_grow` interface needs exactly one new
input: a sum-free 5-colouring of `[1, M]`. Dropping it in means

* `Def.lean`: `v = pin 5 (fun k => ((2*M+1) * 3 ^ (k - 5) - 1) / 2)`, `record = maxWith V001.record v`;
* `Proof.lean`: copy V001 verbatim, replace `col4` by `col5 n = C / 5 ^ n % 5` (base **5**, not
  base 4 — `Nat.mod_lt` then gives `col5 n < 5` for free, which is the `∀ n, c n < k` half of
  `SumFreeCol`), replace `col4_check` by the same `decide +kernel` at `N = M`, and replace
  `4 + j` by `5 + j` in `v_valid`.

Budget estimate: `col4_check` at `N = 44` cost 2885 heartbeats over `45² = 2025` pairs.
At `M = 160` that is `161² = 25921` pairs, so roughly 40000–80000 heartbeats (base-5 powers
are dearer than base-4 ones). V001's whole file was 14096, so the total should stay under the
200000 limit, but it is worth measuring. If it does not fit, pack base **8** instead (a shift
for GMP) as `col n = if n < M + 1 then C / 8 ^ n % 8 else 0` and prove `∀ n, col n < 5` by
`decide` on the `M + 1` cases plus `0 < 5`.

### Why `M = 133` cannot simply be pushed up

The colouring V001 actually reaches at `k = 5` is the tripling extension of `col4`:
`[1,44]` keeps `col4`, `[45,89]` is the fresh colour `4`, `[90,133]` is `col4` translated by
`89`. A depth-first search that fixes that prefix and tries to colour `134, 135, …` with the
same 5 colours **fails immediately at `n = 134`**: the tripling colouring of `[1,133]` is
maximal. So any re-base at `k = 5` needs a genuinely different 5-colouring, not an extension.

### The search

A min-conflicts / tabu local search was written in C (objective: number of monochromatic
`x + y = z` configurations in `[1,N]` under a 5-colouring; move: recolour one element).

* Plain min-conflicts with 8 % noise plateaus at 3 conflicts at `N = 160`.
* Tabu (full neighbourhood scan, tenure `10 + rand(#conflicted)`, aspiration on the
  incumbent) reaches **1 remaining triple** at `N = 160` and at `N = 140, 145, 150`, across
  many seeds and restarts, but never 0 within the ~10 minutes of search this session could
  afford. It is close; a longer run, or a real SAT solver on the (tiny) CNF
  `¬(c_x=i ∧ c_y=i ∧ c_{x+y}=i)`, should finish it.

**Pitfall that cost this session its version.** The *doubling* configuration `x + x = 2x` is
one configuration, while `x + y = z` with `x ≠ y` gives two ordered pairs. If the incremental
delta weights `(x,x,2x)` differently when `x` is recoloured (the "`i` is a summand" term) than
when `2x` is recoloured (the "`i` is the sum" term), the incrementally maintained cost drifts
below the true cost and the search reports a **spurious solution**. One such "solution" at
`N = 160` was produced and had 10 real violations. Fix: weight `(x,x,2x)` as 2 in both terms
and in the total, and re-verify the total from scratch before declaring success — and always
re-check the printed colouring in an independent script before putting it in Lean.

### Recommended order of work for the next session

1. Run the tabu search (or MiniSat/CaDiCaL on the direct CNF — `5·160` variables, `~6400·5`
   clauses, which is trivial for a modern solver) until a sum-free 5-colouring of `[1, 160]`
   is found and *independently verified*. Then the V002 drop-in above is 20 minutes of Lean.
   Gain: `h(k) ≥ 321·3^{k−5}` against V001's `267·3^{k−5}`, a factor `1.202` at every `k ≥ 5`.
2. Only then consider `M = 536` (`k = 6`, Fredricksen–Sweet) — the `decide +kernel` table is
   about `537² ≈ 288000` pairs and will **not** fit the 200000-heartbeat budget as written;
   it needs the sum-freeness check restructured (for instance a per-`x` lemma proved by a
   single `decide` each, with the outer quantifier handled by `Nat.lt` case analysis), and
   `Def.lean` must stay under 64 KB (a base-5 numeral for `M = 536` is ~375 digits, fine).
3. The genuinely asymptotic step is still Abbott–Moser (base `> 3`), with the caveats in the
   previous section: it needs symmetric sum-free partitions of `ℤ_{2N+1}`, which do **not**
   exist at `N = S(k)` for the `k` of interest, so the statement has to be carried with the
   symmetry as an explicit hypothesis on a smaller base.

## Session 2 — `baseline claude-opus-5` (no new version)

No version was accepted this session; the record stands at **V001**. What was tried, so the
next session does not repeat it. All searches were for the drop-in of step 1 above: a sum-free
5-colouring of `[1, M]` with `M ≥ 134`, which V001's `exists_col_grow` turns into
`h(k) ≥ (2M+1)·3^{k−5}` with no new Lean mathematics.

Three searches, all in C, each run for under a minute (the session budget was 10 minutes):

1. **Chronological backtracking** on `n = 1, …, M`, assigning the colours of `n` in random
   order with the standard symmetry break (a new colour may only be opened as the next unused
   index), random restarts every 20000–300000 backtracks. Reaches nothing at `M = 136` or
   above. Plain DFS in increasing `n` is simply the wrong search order here: it commits to the
   colouring of the small numbers, which is where the constraints are densest, and the failures
   surface hundreds of levels deeper.
2. **Symmetric backtracking mod `m = 2M+1`**: search the partition of `ℤ_m \ {0}` directly with
   `c(n) = c(m−n)` imposed, checking after each assignment that neither `n` nor `m−n` closes a
   monochromatic `x + y ≡ z`. This is the Fredricksen–Sweet shape and the constraint propagation
   is much stronger per node, but it also failed at `M = 136, 140, 145, 150, 160` in the time
   available. Worth more time: this is the formulation the published `S(6) ≥ 536` and
   `S(7) ≥ 1680` colourings come from.
3. **Tabu search** with a correct incremental cost (cost = number of *unordered* pairs `{x,y}`
   with `x + y = z ≤ N` and `c x = c y = c z`; the delta for recolouring `n` enumerates the
   triples with `z = n` and the pairs `{n, y}` for `y ≤ N − n`, so the doubling triple
   `{n, n, 2n}` is counted exactly once on both sides — this is the pitfall that produced a
   spurious solution in the previous session). Full-neighbourhood scan, tenure `6 + rand(10)`,
   aspiration on the incumbent. At `N = 145` it did not reach 0 in 45 s.

**Assessment.** The colouring is the whole difficulty; the Lean side is genuinely ~20 minutes
of drop-in work (change `44` to `M`, `89` to `2M+1`, `pin 4` to `pin 5`, re-pack the base-5
numeral, re-run `decide +kernel`). A 10-minute slot is not enough to do both. The next session
should either

* budget a **single** long run (5+ minutes) of search 2 at `M = 160`, with a wider restart
  policy and value ordering biased to the least-used colour, and nothing else until it returns;
  or
* better, install/locate a CNF solver and encode directly — `5·160 = 800` variables, one
  at-least-one clause per element, and one clause `¬(c_{x,i} ∧ c_{y,i} ∧ c_{x+y,i})` per
  `(x ≤ y, x+y ≤ 160, i)`, about `32000` clauses. That is seconds of work for CaDiCaL or
  MiniSat, and none were found on this machine (`which cadical minisat cryptominisat picosat`
  is empty) — a hand-rolled DPLL is not worth writing, but `pip install python-sat` or a
  vendored solver would settle the question immediately.

Whatever the source, **verify the printed colouring in an independent script** before it goes
into `Def.lean`.

---

## Session 3 — `trial claude-fable`

### The literature, corrected and extended

The recurrence behind every good lower bound is the **S-template** construction of
F. Rowley, *A generalised linear Ramsey graph construction*, Australas. J. Combin. 81 (2021)
245–256, as formulated for Schur numbers by R. Ageron, P. Casteras, T. Pellerin, Y. Portella,
A. Rimmel, J. Tomasik, *New lower bounds for Schur and weak Schur numbers*, arXiv:2112.03175
(2022), Definition 2.1 and Theorem 2.3:

> An **S-template** of width `q` with `n + 1` colours is a sum-free colouring of `[1, q]` whose
> `n` non-special classes are also sum-free **modulo `q`** (`x + y > q ⟹ x + y − q` not in the
> class); `q` itself is necessarily special. If `[1, p]` has a sum-free `k`-colouring, then
> `[1, pq + m − 1]` has a sum-free `(n + k)`-colouring, `m` the least special element: write
> `x = (α − 1)q + u`, `u ∈ [1, q]`, keep the template colour of `u` unless it is special, in
> which case use the colour of the row `α` in the base colouring.

The Abbott–Hanson product `S(m+n) ≥ (2S(m)+1)S(n) + S(m)` is the special case of the template
"`[1, a]` coloured, `[a+1, 2a+1]` special" (`q = 2a+1`, `m = a+1`), and Schur's tripling is the
width-3 template. **No symmetry is needed anywhere** — the previous sessions' belief that the
product needs symmetric sum-free partitions of `ℤ_{2N+1}` (which cannot exist at `N = S(k)`,
since a sum-free colouring of `ℤ_P \ {0}` gives `S(k) ≥ P − 1`) was the obstacle; the
non-special classes only have to be sum-free mod `q` *inside the template*, and the base
partition on the right is arbitrary.

Best published templates (per colour added, the multiplier's root is the growth rate):

| step | template | source | rate |
|---|---|---|---|
| `S(k+1) ≥ 3S(k) + 1` | width 3 | Schur | 3 |
| `S(k+2) ≥ 9S(k) + 4` | width 9 | Abbott–Hanson 1972 | 3 |
| `S(k+2) ≥ 10S(k) + 2` | **shifted** template of width 10 with tail | Bengone, Brouk, Grinsztajn, Helbert, Lugherini, Rimmel, Tomasik, arXiv:2607.15034 (July 2026) | 3.162 |
| `S(k+3) ≥ 33S(k) + 6` | width 33, 4 colours, `m = 7` | Rowley 2021 | 3.208 |
| `S(k+4) ≥ 111S(k) + 43` | width 111, 5 colours, `m = 44` | Ageron et al. 2022 | 3.246 |
| `S(k+5) ≥ 380S(k) + 148` | width 380, 6 colours, `m = 149` | Ageron et al. 2022 | **3.281** |
| `S(k+6) ≥ 1160S(k) + 536` | width 1160, 7 colours (not printed) | Ageron et al. 2022 | 3.240 |

Best published values: `S(6) ≥ 536`, `S(7) ≥ 1680` (Fredricksen–Sweet 2000), `S(7) ≥ 1696`
(F. Rowley, *An improved lower bound for S(7) and some interesting templates*, arXiv:2107.03560,
partition only in an `.xls` attachment), `S(8) ≥ 5286` (Rowley), `S(8) ≥ 5362` and
`S(13) ≥ 2038282` (shifted template, 2026), `S(9) ≥ 17803`, `S(10) ≥ 60948`, `S(11) ≥ 203828`,
`S(12) ≥ 644628` (Ageron et al.). Growth rate `≥ 380^{1/5} ≈ 3.28` is still the best known
(checked with a literature consultation in September 2026).

Explicit data that is available as text and was verified independently in Python before use:
Exoo's `[1, 160]` (EJC 1 (1994) #R8, symmetric, listed for `1..80`), Fredricksen–Sweet's
`[1, 536]` and `[1, 1680]` (EJC 7 (2000) #R32, symmetric halves; for 536 the pair `179, 358`
is allowed to differ and does), and the templates of widths 33, 111, 380 (arXiv:2112.03175,
Appendix A; in the printed width-111 table the element 49 is missing — classes 1 and 4 are both
consistent, class 1 was used).

### V002 — `trial claude-fable`

**Bound.** `record = maxWith V001.record H` with the dynamic programme

```
H 0 = 0,  H 1..7 = 1, 4, 13, 44, 160, 536, 1680,
H (k+8) = max (3·H(k+7) + 1) (33·H(k+5) + 6) (111·H(k+4) + 43) (380·H(k+3) + 148).
```

An improvement at **every `k ≥ 5`**, asymptotically by the factor `(380^{1/5}/3)^k ≈ 1.094^k`.
It matches the best published bounds for all `k ≤ 15` except those that use `S(7) ≥ 1696` or the
2026 shifted template.

**Idea.** Formalise the S-template theorem once, for an abstract template (`IsTemplate n q m c`,
a `Prop` structure; `sf_tmplApply`), and feed it templates and partitions given as lists of
bitsets (one `ℕ` per colour class). The kernel verifies the data with `Bool` checkers written
with `Nat.rec` — `chk a N` checks `(a <<< x) &&& a = 0` for every `x < N` in `a`, `chkW` the
wrapped version `((a <<< x) >>> q) &&& a = 0`, plus `chkBelow`, `chkCov` — which the probe
showed to cost about 0.5 heartbeat-units per step (a bounded `∀ x < N` costs ten times more, and
the base-4 numeral of V001 twenty times more per pair). The `[1, 1680]` partition costs 6676,
the whole file 47211 of 200000. `good_H : ∀ k ≥ 1, ∃ c, SF k (H k) c` is a strong induction.

**Witness.** `n₀ = 5`: `133 < 160`.

### Where the bound stands

| k | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 |
|---|---|---|---|---|---|---|---|---|---|
| V001 | 133 | 400 | 1201 | 3604 | 10813 | 32440 | 97321 | 291964 | 875893 |
| **V002** | **160** | **536** | **1680** | **5286** | **17803** | **60948** | **203828** | **638548** | **2011290** |
| best published | 160 | 536 | 1696 | 5362 | 17803 | 60948 | 203828 | 644628 | 2038282 |

### What the next improvement would take

1. **Rowley's `S(7) ≥ 1696`** (arXiv:2107.03560, ancillary `Specimens_S_7____TFTs-4,5,6.xls`):
   parse the spreadsheet (no `xlrd` on the machine; the file is a genuine OLE2/BIFF workbook),
   verify, pack as 7 bitsets, and add `good7' : Good 7 1696` — `sf_colOf` does the rest. Improves
   `k = 7, 12, 17, …` by about 1 %.
2. **The shifted template** `S(k+2) ≥ 10S(k) + 2` (arXiv:2607.15034, Table II): width 10, two
   new colours `A, B`, shifts `{−1, 0}` only, first row `B A P₀ P₀ B A A B P₀ P₀`, other rows
   `P₋₁ B P₀ P₀ B A A B P₀ P₀`, tail `A B`. Needs a new theorem (a variant of `sf_tmplApply` in
   which the special cells take the colour of row `α` or `α − 1`, plus a tail); the admissibility
   is a finite check over column pairs. Improves `k = 8, 13, 18, …` by about 1.4 %.
3. **Better templates by SAT** (`cadical` is on the machine): a 7-colour template of width
   `> 1250` would raise the growth rate above `380^{1/5}`; Ageron et al. say their width-1160
   one "can definitely be improved by a wide margin". A symmetric restriction and the
   Fredricksen–Sweet depth heuristic are the known aids. High value, uncertain.

### V003 — `trial claude-fable`

**Bound.** `record = maxWith V002.record H` with

```
H 0 = 0,  H 1..7 = 1, 4, 13, 44, 160, 536, 1696,
H (k+8) = max (3·H(k+7)+1) (10·H(k+6)+2) (33·H(k+5)+6) (111·H(k+4)+43) (380·H(k+3)+148).
```

Improves V002 at every `k ≡ 2, 3 (mod 5)`, `k ≥ 7` (by about 1 % and 1.4 %), and equals the
best published lower bound at every `k ≤ 15`.

**Idea.** (1) Rowley's `S(7) ≥ 1696` partition, read from the `.xls` attachment of
arXiv:2107.03560 with `xlrd` installed into the scratch directory, verified, and checked by the
kernel through V002's `sf_colOf` (`good7`, 6746 heartbeats). (2) The **shifted S-template**
theorem of arXiv:2607.15034 for shift set `{−1, 0}` with a tail, `sf_shApply`, proved for an
abstract template whose admissibility is a finite check over column pairs and first-row flags;
Lean cannot synthesise `Decidable` for three nested bounded quantifiers over an implication, so
the check is a `Bool` of nested `List.all` (`admCheck`) with a conversion lemma. The width-10
template of the paper gives `step10 : Good k N → 1 ≤ N → Good (k+2) (10N+2)`.

**Budget.** 105959 heartbeats; the 27-way case analysis of the block was first inlined in
`sf_shApply` and cost 155260 — moving it to a lemma with only the needed hypotheses
(`block_case`) cut it to 51522. `omega` in a large context is the expensive part.

**Witness.** `n₀ = 7`: `1680 < 1696`.

### Where the bound stands (after V003)

| k | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 |
|---|---|---|---|---|---|---|---|---|---|
| V002 | 1680 | 5286 | 17803 | 60948 | 203828 | 638548 | 2011290 | 6765288 | 23160388 |
| **V003** | **1696** | **5362** | 17803 | 60948 | 203828 | **644628** | **2038282** | 6765288 | 23160388 |
| best published | 1696 | 5362 | 17803 | 60948 | 203828 | 644628 | 2038282 | 6765288 | 23160388 |

### Searches tried after V003 (`cadical`), so far without result

* A symmetric 7-colouring of `[1, N]`, `N ∈ {1697, 1700, 1706}`, with Rowley's colouring fixed
  on `[1, 537]` and mirrored: UNSAT in seconds each. Fredricksen–Sweet's `[1, 536]` as the
  fixed base does not even reach 1696 (UNSAT).
* A symmetric 6-colour S-template of width 381 with least special element `≥ 100`
  (`tmplsearch.py` in the scratch directory: sum-free classes, non-special classes sum-free
  mod `q`, `q` special): UNSAT in seconds. Any 6-colour template of width `≥ 381` would beat
  V003 at every `k ≡ 0 (mod 5)` and raise the growth rate above `380^{1/5}`.

### State at the end of session 3 (closed by the maintainers)

Accepted this session: **V002** (`h(k)` from the S-template dynamic programme, improves every
`k ≥ 5`) and **V003** (`S(7) ≥ 1696` and the shifted template `10·S(k) + 2`). The open version
is **V004**; no directory was scaffolded for it and nothing is half-written in the record tree.

**Unfinished exploration** (all files in the scratch directory `.lake/scratch/Schur-Lower/fable/`,
which persists between sessions):

* `partitions.json` — verified colourings of `[1, 160]`, `[1, 536]`, `[1, 1680]`, `[1, 1696]`
  (0-based colour per element); `templates.json` — the verified templates of widths 33, 111,
  380 with their special colour and `m`. `parse_partitions.py`, `templates.py` produced them
  from the papers' text (`exoo1994.txt`, `fs2000.txt`, `ageron.txt`, `shifted.txt`,
  `rowley_s7.txt`, `rowley.xls`; `pylib/` holds `xlrd`).
* `Dev.lean`, `Dev3.lean` — the development files that became V002's and V003's `Proof.lean`.
* `tmplsearch.py q K sym m timeout` — `cadical` search for an S-template of width `q` with `K`
  colours (special last): `sym = 1` imposes `c(u) = c(q − u)`, `sym = 2` the paper's symmetry
  (the derived colouring of `[1, q + m − 1]` is a palindrome, `m` exact), which all three
  published templates have. Results so far: `q = 381, K = 6, sym = 1, m ≥ 100`: UNSAT in
  seconds; `q = 380, K = 6, sym = 1, m ≥ 100` and `q = 380, K = 6, sym = 2, m = 149` (the
  sanity checks that should re-find the published template): **no answer within 600 s** —
  so this encoding is not yet strong enough to reproduce the paper's search, let alone beat it.
  Ideas not yet tried: fix the special colour to be the last to appear and bound the least
  elements of the classes as Ageron et al. did; seed from the published 380 template and search
  a neighbourhood; local search instead of CDCL; `K = 7` with `q ≥ 1275` (beats V003 at every
  `k ≡ 1 (mod 5)`), where Ageron et al. only report the width-1160 template built from the 536
  partition.
* `symsearch2.py N base B K timeout` — symmetric sum-free `K`-colouring of `[1, N]` with a fixed
  prefix `[1, B]` of a known colouring (and its mirror). With Rowley's `[1, 537]` prefix:
  `N = 1697, 1700, 1706` UNSAT. Shorter prefixes were not tried.

**Recommended next version (V004).** In decreasing order of value: (1) any 6-colour S-template
of width `≥ 381` (new growth rate; needs the search above to work); (2) a 7-colour template of
width `≥ 1275`, or a 5-colour one of width `≥ 112` (non-symmetric; Ageron et al. only excluded
symmetric ones up to 118); (3) a direct improvement of `S(6) ≥ 536` or `S(7) ≥ 1696` by SAT.
Whatever is found, the Lean side is a drop-in: a plain partition goes through `V002.sf_colOf`,
an S-template through `V002.isTemplate_colOf` + `V002.good_step`, a shifted template through
`V003.adm_of_check` + `V003.sf_shApply`, and the dynamic programme `H` gets one more `max` arm
and, for a partition, one more base case.
