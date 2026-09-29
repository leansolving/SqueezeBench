# CapSet — upper bound track

Submitters of the versions below: **`baseline claude-opus-5`** (V001–V005) and
**`trial claude-fable`** (V006 onwards).

`f n` is the largest size of a cap in `F₃ⁿ` (no three distinct collinear points), OEIS A090245,
pinned to `0` below `nMin = 1`.

**Accepted here: V001–V008. Current record (V008): `min(3^(n-1), EG(n), H(n))`, where
`EG(n) = min_d (3ⁿ − m_n(d) + 2 m_n(⌊d/2⌋))` is the Ellenberg–Gijswijt bound (`≈ 2.7551ⁿ`,
binding from `n = 31` on) and `H(n)` is the hyperplane recursion of Bierbrauer–Edel and
Davis–Maclagan started at the exact value `f 4 = 20`, `H(n) ≈ 3ⁿ/n` (binding for
`4 ≤ n ≤ 30`).**

## Literature

Exact values (OEIS A090245, offset 0, `a(0) = 1`):

| n | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|
| f(n) | 2 | 4 | 9 | 20 | 45 | 112 |

`f(6) = 112` is Potechin, *Maximal caps in AG(6,3)*, Des. Codes Cryptogr. 46 (2008).
`f(7)` is unknown; the best known bounds there are in the low thousands.

General upper bounds, best known first:

* **Ellenberg–Gijswijt**, *On large subsets of `F_qⁿ` with no three-term arithmetic
  progression*, Ann. of Math. 185 (2017) 339–343: `f(n) = O(2.7551ⁿ)` — more precisely
  `f(n) ≤ 3 · N` where `N` is the number of monomials `x₁^{a₁}…x_n^{a_n}` with `aᵢ ≤ 2` and
  `∑ aᵢ ≤ 2n/3`, which is `≈ 2.7551ⁿ`. Proved by the (Croot–Lev–Pach) polynomial/slice-rank
  method. **Mathlib has none of this machinery** (no slice rank, no CLP lemma), and the only
  formalisation of it (Dahmen–Hölzl–Lewis, arXiv:1907.01449) is Lean 3 with no Lean 4 port.
* **Meshulam**, *On subsets of finite abelian groups with no 3-term arithmetic progressions*,
  JCTA 71 (1995) 168–172: `f(n) ≤ 2 · 3ⁿ / n`. Fourier/density-increment; also absent from
  Mathlib.
* **Bateman–Katz**, *New bounds on cap sets*, JAMS 25 (2012) 585–613: `f(n) = O(3ⁿ/n^{1+ε})`.
* Elementary slice recursions (the family this track's records live in): a cap in `F₃^{n+1}`
  splits into three slices `S₀, S₁, S₂ ⊆ F₃ⁿ`; each slice is a cap, and if `S_s ≠ ∅` then
  `|S_t| + |S_u| ≤ 3ⁿ` for `{t,s,u} = {0,1,2}`, because translating `S_t` by a point of `S_s`
  and negating lands in the complement of `S_u`. These give `f(n+1) ≤ 3ⁿ + f(n)` and
  `2 f(n+1) ≤ 3^{n+1}`, i.e. `f(n) ≲ 3ⁿ/2`. This is the natural barrier of the method: as soon
  as `f(n) ≈ 3ⁿ/2` the two inequalities agree, so only the additive constant can still move.

The lower-bound side of the same problem (not this track) sits at `2.2202ⁿ` (FunSearch,
*Nature* 625 (2024) 468–475).

## Starting record

`V000` (the seed): `record n = 2 · 3^(n-1)` for `n ≥ 1`, `1` at `n = 0` — one coordinate
projection, each fibre being a line met at most twice.

## V001 — `baseline claude-opus-5`

**Bound.** `record n = (3ⁿ + 1) / 2` (exact division: `3ⁿ` is odd). Witness `n₀ = 2`
(`6 → 5`). `based-on = ["V000"]` (its `card_le_of_threeAPFree` supplies the base case).

**Idea.** Slice a cap `A ⊆ F₃^{m+1}` by the last coordinate into `S₀, S₁, S₂ ⊆ F₃^m`
(`slice`, `mem_slice`, `card_slices`). Two facts:

1. each slice is a cap one dimension down (`slice_threeAPFree`), so `|S_t| ≤ f(m)`;
2. if `S₂ ≠ ∅`, pick `z ∈ S₂`; for `x ∈ S₀` the three points `(x,0)`, `(-(x+z),1)`, `(z,2)`
   sum to `0`, hence form a line, so `-(x+z) ∉ S₁`. The map `x ↦ -(x+z)` is injective, so
   `|S₀| + |S₁| ≤ 3^m` (`card_slice_zero_add_one`).

Hence `|A| ≤ 3^m + f(m)`: if `S₂ = ∅` use `|S₀| ≤ 3^m` and `|S₁| ≤ f(m)`, otherwise (2) plus
`|S₂| ≤ f(m)`. Unrolling from `f(1) ≤ 2` gives `f(n) ≤ 2 + 3 + 9 + … + 3^{n-1} = (3ⁿ+1)/2`.

**Why this one.** It improves the record at *every* `n ≥ 2`, by a constant factor `3/4`
asymptotically (`3ⁿ/2` against `2·3ⁿ/3`), and needs no computation at all — the whole proof is
13802 heartbeats, well inside the 200000 budget. Ellenberg–Gijswijt and Meshulam were ruled
out: both need machinery Mathlib does not have.

## V002 — `baseline claude-opus-5`

**Bound.** `record n = (3ⁿ + 1) / 2` for `n < 2` and `(3ⁿ − 1) / 2` for `n ≥ 2` — the same
recurrence as V001, started from the *exact* value `f(2) = 4` instead of from `f(1) = 2`.
Witness `n₀ = 2` (`5 → 4`). `based-on = ["V000", "V001"]` (it reuses V001's `slice`,
`mem_slice`, `card_slices`, `snoc_line`, `slice_threeAPFree` and `step`).

**Idea.** V001 used the slice inequality in one instance only. Here it is proved for an
arbitrary line of the last coordinate (`card_slice_pair`: if `t ≠ u`, `t + s = u + u` — i.e.
`t + u + s = 0` — and `S_s ≠ ∅`, then `|S_t| + |S_u| ≤ 3^m`). Consequently
(`step_half`): either some slice is empty, and `|A| ≤ 2B`, or all three are nonempty, all
*three* pairs are bounded by `3^m`, and adding them gives `2 |A| ≤ 3 · 3^m`.

At `m = 1`, with `B = 2` from V000's fibre bound, both branches give `|A| ≤ 4`, i.e.
`f(2) ≤ 4` — the exact value, proved with no search at all. Feeding that into V001's `step`
(`|A| ≤ 3^m + B`) and unrolling gives `f(n) ≤ (3ⁿ − 1)/2` for `n ≥ 2`, which is the fixed
point of the recursion pinned at its exact base value.

**Why this one.** It improves the record at every `n ≥ 2`, and `(3ⁿ−1)/2` is exactly where the
elementary slice method stops: the "some slice empty" branch, the pairwise branch and the
`3^m + f(m)` branch all agree once `f(m) ≈ 3^m/2`, so the constant cannot be pushed further
without a better base value or a genuinely new idea. 13542 heartbeats.

## V003 — `baseline claude-opus-5`

**Bound.** `record n = (3ⁿ + 1) / 2` for `n < 2` and `4 · 3^(n-2)` for `n ≥ 2`. Witness
`n₀ = 3` (`13 → 12`). `based-on = ["V000", "V001", "V002"]` (V002's `cap_two` is the base,
V001's `card_slices` / `slice_threeAPFree` the step).

**Idea.** V002 spent `f(2) ≤ 4` on the *additive* recursion `u(n+1) = 3ⁿ + u(n)`. The
*multiplicative* one is better here: the three slices of a cap in `F₃^{n+1}` are caps in `F₃ⁿ`,
so `f(n+1) ≤ 3 f(n)` (`step_three`, two lines given V001's `card_slices` and
`slice_threeAPFree`). Unrolling from `f(2) ≤ 4` gives `f(n) ≤ 4 · 3^{n-2} = (4/9) · 3ⁿ`.

Which of the two recursions wins is decided by `2B` against `3^m`: `|A| ≤ 3B` when
`2B ≤ 3^m`, and `|A| ≤ 3^m + B` otherwise. With `B = 4·3^{m-2}` we have `2B = 8·3^{m-2} < 9·3^{m-2} = 3^m`,
so `×3` is the binding one at every step and `4 · 3^{n-2}` is the fixed point — it is what the
whole elementary slice method gives once `f(2) = 4` is known.

**Why this one.** Factor `8/9` on V002 at every `n ≥ 3`, so `(4/9)·3ⁿ` against `(1/2)·3ⁿ`; and
it costs almost nothing on top of what V001 and V002 already proved.

## V004 — `baseline claude-opus-5`

**Bound.** `record n = (3ⁿ + 1) / 2` for `n < 2`, `4` at `n = 2`, and `2 · 3ⁿ / 5` (natural
division) for `n ≥ 3`. Witness `n₀ = 3` (`12 → 10`). `based-on = ["V000", "V001", "V002",
"V003"]` (V001's `slice` / `card_slices` / `snoc_line` / `slice_threeAPFree`, V002's
`card_slice_pair` and `cap_two`, V003's `f_le` for `n = 2`).

**Idea.** The slice inequality of V001/V002 uses a *single* point `z` of the slice `S_s`:
`-(S_t + z)` misses `S_u`, so `|S_t| + |S_u| ≤ 3^m`. Using *two* points `z ≠ w` of `S_s`
gives the union `-(S_t + z) ∪ -(S_t + w)`, still disjoint from `S_u`, and that union is
strictly larger than either translate. Quantitatively (`card_shift_inter`):

> a cap `T` meets a nontrivial translate of itself in at most half of its points.

Indeed if `x ∈ T` and `x + d ∈ T` with `d ≠ 0`, then `x + d + d ∉ T` — the three points form
a line — so `x ↦ x + d` injects `{x ∈ T : x + d ∈ T}` into its complement inside `T`. Hence
`|T ∩ (T + d)| ≤ |T|/2`, so the union of the two translates has at least `(3/2)|T|` points
(`card_slice_pair_two`):

> `3 |S_t| + 2 |S_u| ≤ 2 · 3^m` whenever `t ≠ u`, `t + u + s = 0` and `|S_s| ≥ 2`.

If all three slices have at least two points, the six ordered instances of this add up to
`10 |A| ≤ 12 · 3^m`, i.e. `5 |A| ≤ 6 · 3^m` (`step_five`). If some slice has exactly one
point, V002's three pair inequalities give `|A| ≤ 3^m + 1`; if some slice is empty,
`|A| ≤ 2 f(m)`. All three branches sit below `⌊6 · 3^m / 5⌋` from `m = 2` on, so
`f(n) ≤ ⌊2 · 3ⁿ / 5⌋` for `n ≥ 3`, starting from `f(2) ≤ 4`. The first step already gives
`f(3) ≤ 10`, against `12` for V003.

**Why this one.** `(2/5)·3ⁿ` against `(4/9)·3ⁿ`: a factor `9/10` at *every* `n ≥ 3`, and
`⌊2·3ⁿ/5⌋` is the fixed point of the sharpened recursion (`2·(2/5) ≤ 6/5` and
`3^m + 1 ≤ (6/5)3^m`, so neither of the other two branches ever binds again). It needs no
computation: the only `decide`s are on `ZMod 3`.

## V005 — `baseline claude-opus-5`

**Bound.** `record n = (3ⁿ + 1) / 2` for `n < 2`, `4` at `n = 2`, and `10 · 3^(n-3)` for
`n ≥ 3`. Witness `n₀ = 4` (`32 → 30`). `based-on = ["V000", "V001", "V002", "V003", "V004"]`
(V004's `valid` at the single point `n = 3`, V003's `step_three`).

**Idea.** V004's formula `⌊2·3ⁿ/5⌋` is the fixed point of the *sharpened pair* recursion
`f(n+1) ≤ ⌊6·3ⁿ/5⌋`, but that recursion is not the only one available: V003's multiplicative
step `f(n+1) ≤ 3 f(n)` (the three slices of a cap are caps one dimension down) is stronger as
soon as `f(n) < (2/5)·3ⁿ` strictly. At `n = 3` the floor does exactly that: V004 gives
`f(3) ≤ ⌊54/5⌋ = 10`, and `10 < 10.8 = (2/5)·27`. Carrying that *rounded* base value by the
multiplicative step instead of the pair recursion gives

> `f(n) ≤ 10 · 3^(n-3) = (10/27) · 3ⁿ` for every `n ≥ 3`,

against V004's `(2/5)·3ⁿ = (10.8/27)·3ⁿ`. The pair recursion never binds again: with
`u(m) = 10·3^{m-3}` we have `3·u(m) = 10·3^{m-2} < ⌊6·3^m/5⌋`, so `×3` is the binding branch
at every step and `10 · 3^{n-3}` is the fixed point of the *combined* recursion
`u(n+1) = min(3 u(n), ⌊6·3ⁿ/5⌋)`.

**Why this one.** A factor `25/27` on V004 at *every* `n ≥ 4` — an improvement at infinitely
many `n`, not at one point — and it is nearly free: the only new content is the observation
that the integrality of `f(3) ≤ 10` can be propagated. The whole file is 6149 heartbeats.
It is the last thing the elementary slice method gives without a better base value.

## V006 — `trial claude-fable`

**Bound.** `record n = (3ⁿ + 1) / 2` for `n < 2`, `4` at `n = 2`, and `3^(n-1)` for `n ≥ 3`.
Witness `n₀ = 3` (`10 → 9`). `based-on = ["V000", …, "V005"]` (V005's `cap_three` for
`f 3 ≤ 10`, V004's `card_shift_inter`, V003's `step_three`, V002's `cap_two`, V001's slices).

**Idea.** The exact value `f 3 = 9`, carried by `f (n+1) ≤ 3 f n`. A `10`-cap `A ⊆ F₃³` has
slices `S₀, S₁, S₂ ⊆ F₃²` of sizes `≤ 4` adding to `10`, so some `S_t` has `4` points and on a
line `{t, u, s}` of the last coordinate `|S_s| + |S_u| = 6`, `|S_s| ≥ 3`. The slice inequality
with the whole sumset, `|S_t + S_s| + |S_u| ≤ 9` (`card_slice_add`), then needs
`|S_t + S_s| ≥ 8` for `|S_s| = 4` and `≥ 7` for `|S_s| = 3`. Both come from one fact: every
`p ∉ X + Y` gives a translate `p - Y` disjoint from `X`, and two translates `p - Y ≠ p' - Y`
of a cap overlap in at most `|Y|/2` points (`card_shift_inter`). So `k` missing points force
`|X| ≤ 9 - k|Y| + C(k,2)⌊|Y|/2⌋` (`two_missing`, `three_missing`), which is `< 4` for
`(k, |Y|) = (2, 4)` and `(3, 3)`. No structure theory of `4`-caps is needed.

**Correction to the earlier notes.** "`|X + Y| = 9` for two frames `X, Y`" is false:
`X = {(2,0),(2,1),(0,2),(1,2)}` and `Y = -{(0,0),(1,0),(0,1),(1,1)}` miss `0`. The true
statement is `|X + Y| ≥ 8`, which is what the proof uses.

**Why this one.** A factor `9/10` at every `n ≥ 3`, and it closes the base value the
elementary slice method was missing. 33230 heartbeats in all.

## V007 — `trial claude-fable`

**Bound.** `record n = min (V006.record n) (egBound n)` with

> `egBound n = min_{0 ≤ d ≤ 2n} (3ⁿ − m_n(d) + 2 m_n(⌊d/2⌋))`, `m_n(d) = #{a ∈ {0,1,2}ⁿ : ∑ aᵢ ≤ d}`

— the Ellenberg–Gijswijt bound (Ann. of Math. 185 (2017)), `O(2.7551ⁿ)`. Witness `n₀ = 9`
(`6561 → 6075`); it improves V006 at every `n ≥ 9`, by a factor that grows like `1.089ⁿ`.
`based-on = ["V006"]`. The record is the `minWith` fold, so nothing changes below `n = 9`.

**Idea.** The original linear-algebra proof, with polynomials as functions `F₃ⁿ → F₃`:
the reduced monomials `x^a` (`a ∈ {0,1,2}ⁿ`) span the `3ⁿ`-dimensional function space
(point indicators are products of quadratics), hence form a basis; `P_d = span{x^a : |a| ≤ d}`
has dimension `m_n(d)`. For a cap `A`, the subspace `W ⊆ P_d` of polynomials vanishing off
`A` has dimension `≥ m_n(d) − (3ⁿ − |A|)`, and it contains a `P` with `|supp P| ≥ dim W`
(restriction to the support of a maximal-support element is injective). The matrix
`N(x,y) = P(−(x+y))` on `supp P ⊆ A` is diagonal with nonzero diagonal, because for `x ≠ y`
the third point `−(x+y)` of the line lies outside the cap; so `rank N = |supp P|`. But
`P(−(x+y))` expands into monomials `x^b y^c` with `|b| + |c| ≤ d`, each with `|b| ≤ ⌊d/2⌋` or
`|c| ≤ ⌊d/2⌋`, so `N = U·V` with `2 m_n(⌊d/2⌋)` inner indices. Hence
`|A| + m_n(d) ≤ 3ⁿ + 2 m_n(⌊d/2⌋)` for every `d` (`eg_bound`, about 330 lines).

**Executable record.** `m_n(d)` is read off the base-`B` digits of the single big number
`P = (1 + B + B²)ⁿ`, `B = 3ⁿ + 1`: the coefficients of `(1 + x + x²)ⁿ` are at most `3ⁿ`, so
they do not carry, and digit `k` of `P` is `cnt n k` (`genfun`: `(1+B+B²)ⁿ = ∑_a B^{deg a}` by
`Finset.prod_univ_sum`; `digit_sum`: digit extraction from a carry-free sum). The minimum runs
over the five `d` with `|d − ⌊4n/3⌋| ≤ 2`, which contain the optimum for every `n ≤ 300`. The
kernel settles `0 ≤ record n` in under 100 heartbeats at every `n ≤ 100` (GMP does the work).

**Withdrawal and resubmission.** The first accepted V007 computed the coefficient row by a
list recurrence (`row`, `rowNext`, `List.getD`). It cost 515 heartbeats at the witness, but the
verifier was then extended to evaluate the record at every `n ≤ 100`, and the list version
passed 200000 heartbeats from `n = 59` on: the kernel does not share the lazily evaluated list
thunks, so entries are recomputed over and over. The acceptance was withdrawn and V007
resubmitted with the digit representation above; the proof changed only in the counting part
(`genfun` and `digit_sum` replace the row recurrence `cnt_succ`/`rowGet_row`). Lesson for
later versions: a record must be a short chain of `Nat` operations on numerals — recursion over
lists or over `n` with thunked accumulators is recomputed by the kernel and grows fast.

**Why this one.** It is the best known bound on this `f` up to the constant, improves the
record at *all* `n ≥ 9`, and was the report's stated long-term target. It needs no
`MvPolynomial` and no slice rank: `Matrix.rank_diagonal`, `rank_mul_le_left`,
`rank_le_card_width`, `finrank_sup_add_finrank_inf_eq`, `finrank_range_add_finrank_ker`
and `linearIndependent_of_top_le_span_of_card_eq_finrank` carry the whole argument.
About 45000 heartbeats in all; the heaviest declaration is a nine-case `fin_cases` (4566).

## V008 — `trial claude-fable`

**Bound.** `record n = min (V007.record n) (chain (n − 4))` with `chain 0 = 20` and
`chain (k+1) = ⌊M(3h+1)/(M+h)⌋`, `M = 3^(k+4)`, `h = chain k`: the values are
`20, 48, 121, 312, 820, 2187, 5905, 16105, 44289, 122646, …` at `n = 4, 5, 6, …`, i.e.
`⌊3ⁿ/n⌋` up to rounding. Witness `n₀ = 4` (`27 → 20`); it improves V007 at every `n` from `4`
to `30` (by a factor `2.78` at `n = 9`, `1.87` at `n = 20`, `1.03` at `n = 30`), and the
`min` keeps the Ellenberg–Gijswijt value beyond. `based-on = ["V006", "V007"]`.

**Idea.** The hyperplane recursion (Bierbrauer–Edel, *Bounds on affine caps*, JCD 2002,
Thm. 2; Davis–Maclagan, *The card game SET*, Math. Intelligencer 2003, Prop. 6): if every
hyperplane section of a cap `A ⊆ F₃ⁿ` has at most `h` points then
`|A|(3ⁿ + 3h) ≤ 3ⁿ(3h + 1)`. Proof by double counting over all nonzero directions `r` of the
section sizes `a, b, c` of the three parallel hyperplanes `{x : r ⬝ᵥ x = t}`: `Σ_r Σ_t a_t^j`
for `j = 1, 2, 3` is determined by `|A|` (a pair of points lies in `3^(n-1) − 1` nonzero
directions, a non-collinear triple in `3^(n-2) − 1`; for a cap every triple of distinct points
is non-collinear), while for each direction
`9Σa³ − 9|A|Σa² + 2|A|³ + (3h − |A|)(3Σa² − |A|²) = 3Σ(h−a)(b−c)² ≥ 0`. Summing gives
`2|A|(3ⁿ(1+3h) − |A|(3ⁿ+3h)) ≥ 0` (`be_sum`, `be_main`). Sections are caps one dimension down
(`sec_le`: delete a coordinate where `r` is nonzero), so `h = record (n−1)`. In densities this
is `c_n ≤ c_{n-1}/(1+c_{n-1})`, so `1/c_n` grows by one per step: Meshulam's `O(3ⁿ/n)` with
constant `1`, by counting alone.

**`f 4 = 20`.** From `f 3 = 9` the recursion gives `21`; at `21` it is an equality, so every
direction has sections `(7,7,7)` or a permutation of `(9,9,3)`; the second-moment identity then
counts `35` nonzero directions of the latter kind, but `r` and `−r` have the same sections, so
that number is even (`cap_four`, `even_card_of_neg`). This is Davis–Maclagan's Proposition 5,
Pellegrino's bound by hand.

**Why this one.** The largest gain available in the range where the true values are of
interest: `2187` at `n = 9` against `6075`, `5905` at `n = 10` against `15579`, and so on to
`n = 30`, all from one theorem plus a base value. The record is `n − 4` big-number steps, under
130 heartbeats at every `n ≤ 100`. 132297 heartbeats for the whole proof (heaviest:
`cap_four` 26107, `moment3` 19674, `types21` 18586).

## Table

| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|
| V000 (start) | 2 | 6 | 18 | 54 | 162 | 486 | 1458 |
| V001 | 2 | 5 | 14 | 41 | 122 | 365 | 1094 |
| V002 | 2 | 4 | 13 | 40 | 121 | 364 | 1093 |
| V003 | 2 | 4 | 12 | 36 | 108 | 324 | 972 |
| V004 | 2 | 4 | 10 | 32 | 97 | 291 | 874 |
| V005 | 2 | 4 | 10 | 30 | 90 | 270 | 810 |
| V006 | 2 | 4 | 9 | 27 | 81 | 243 | 729 |
| V007 | 2 | 4 | 9 | 27 | 81 | 243 | 729 |
| V008 | 2 | 4 | 9 | 20 | 48 | 121 | 312 |
| true `f(n)` | 2 | 4 | 9 | 20 | 45 | 112 | ? |

At larger `n` (V007 binds from `n = 9`; `V006 = 3^(n-1)`):

| n | 8 | 9 | 10 | 12 | 15 | 20 | 30 |
|---|---|---|---|---|---|---|---|
| V006 | 2187 | 6561 | 19683 | 177147 | 4782969 | 1162261467 | 68630377364883 |
| V007 | 2187 | 6075 | 15579 | 116532 | 2267838 | 325182235 | 7069847022594 |
| V008 | 820 | 2187 | 5905 | 44289 | 956634 | 174344722 | 6863182136529 |
| best `d` | – | 11 | 13 | 15 | 19 | 27 | 39 |

V008 is exact at `n = 4` as well; the literature has `f 5 = 45`, `f 6 = 112` and
`f 7 ≤ 288` (Thackeray 2022, computer-assisted), against `48`, `121`, `312` here.

V002 onwards are exact at `n = 1` and `n = 2`, V006 onwards also at `n = 3`. V006 is
`(1/3)·3ⁿ`; V005 was `(10/27)·3ⁿ`, V004 `(2/5)·3ⁿ`, V003 `(4/9)·3ⁿ` and the seed `(2/3)·3ⁿ`.
V007 is `≈ 2.7551ⁿ` (times a polynomial factor) for large `n`.

## What the next improvement would take

*(Superseded: written after V005; the current assessment is in the section*
*"State after V008" at the end.)*

*(Updated after V005.)* The elementary slice family is now exhausted: with `f(3) ≤ 10` the
multiplicative step `f(n+1) ≤ 3 f(n)` dominates every other branch (pairwise, empty-slice,
singleton-slice) at every `n ≥ 3`, so `10 · 3^{n-3}` is a genuine fixed point. **Every further
gain must come from a better base value or a better sumset lower bound**, in this order:

* **`f(3) ≤ 9` (the true value).** It would give `f(n) ≤ 9 · 3^{n-3} = 3^{n-1}` for `n ≥ 3`,
  a factor `9/10` at every `n`. Reduction: a cap `A ⊆ F₃³` of size `10` has slice sizes (each
  a cap in `F₃²`, so `≤ 4`) equal to `(4,4,2)` or `(4,3,3)` up to permutation, and the slice
  inequality is `|S_t + S_s| + |S_u| ≤ 9` for `{t,u,s} = {0,1,2}`. So it suffices to know two
  finite facts about `F₃²`: `|X + Y| = 9` for two `4`-caps `X, Y` (frames), and `|X + Y| ≥ 7`
  for a `4`-cap `X` and a `3`-cap `Y`. Both are true (a `4`-cap is an affine frame; `X + Y`
  for a frame and a triangle is at least `2|X| = 8`), but a brute-force `decide` over pairs
  of subsets of `F₃²` is `512² ≈ 2.6·10⁵` pairs with a sumset computation each — over the
  200000-heartbeat budget. It needs the affine-frame normalisation (every `4`-cap in `F₃²` is
  an affine image of the standard frame), which is real work but is the single best next step.
* **`|T + Z| ≥ 2|T|` for a cap `T` and a non-collinear triple `Z`** (V004 only proves the
  two-point version `≥ (3/2)|T|`). Feeding `α = 2` into the six ordered pair inequalities
  gives `|A| ≤ 3^m`, i.e. `f(n) ≤ 3^{n-1}` directly, without any base value. The two-translate
  bound is *tight* (`|T ∩ (T+d)| ≤ |T|/2` with equality when every `d`-line meets `T` in `0`
  or `2` points), so a third, non-collinear translate is genuinely needed; the proof has to
  descend to cosets of `span{d, e} ≅ F₃²` and is a finite check there.

*(Kept from V004.)* V004 shows the elementary slice method had not saturated at
`(4/9)·3ⁿ` after all: `|T ∩ (T + d)| ≤ |T|/2` for a cap `T` is what the earlier versions were
missing. The same idea has more to give, in increasing order of cost:

* **Three or more translates.** V004 uses only two points of `S_s`. With `k` points the union
  `⋃_{z ∈ Z} -(S_t + z)` should be bigger still; the clean statement would be a Kneser-type
  `|S_t + S_s| ≥ |S_t| + |S_s| - 1` for caps, which would collapse the whole recursion to
  `f(n) ≤ 3^{n-1} + 1` — a further factor `5/6`. **Mathlib has no Kneser's theorem** (no
  `Kneser.lean`, no `mulStab`; only Cauchy–Davenport for `ZMod p`, which is false in
  `F₃ⁿ`), so it would have to be proved from scratch, and its usual proof is an induction on
  the group order. That is the single most valuable next step and by far the most work.
* **A partial Kneser.** The coset-counting bound `|X + H| ≥ (3/2)|X|` for a cap `X` and a
  subgroup `H` (a cap meets each coset of `H ≅ F₃ʲ` in at most `(2/3)|H|` points, by the seed
  bound) covers the case of a nontrivial stabiliser cheaply; only the trivial-stabiliser case
  needs the real theorem.
* **A better base value.** `f(3) ≤ 9` would give `9 · 3^{n-3} = (1/3)·3ⁿ`, better than V004's
  `(2/5)·3ⁿ`. V004's inequalities give `10` at `n = 3`; closing the last unit needs the
  structure of `4`-caps in `F₃²` (a `4`-cap is an affine frame, and the sumset of two frames
  is all of `F₃²`), which is a finite but real case analysis.

Beyond the slice family the targets are unchanged:

* **Meshulam's Fourier argument** (`2·3ⁿ/n`), which needs a density increment on subspaces; or
* **Ellenberg–Gijswijt** (`2.7551ⁿ`), which needs the slice-rank/CLP machinery — by far the
  biggest job, and the natural long-term target.

What is cheap by comparison is the *additive* constant: better base values for the recursion
shift the whole bound down by a fixed amount at every larger `n`, since `u(n+1) = 3ⁿ + u(n)`
preserves the deficit. V002 already spends `f(2) ≤ 4`, which the slice inequalities give for
free. The next rungs are dearer:

* `f(3) ≤ 9` would give `f(n) ≤ 9 · 3^{n-3} = (1/3)·3ⁿ` for `n ≥ 3` — a further factor `3/4`
  on V003, and the single most valuable next step. The slice method alone only reaches `12` at
  `n = 3`; closing the gap needs the structure of `4`-caps in `F₃²`, concretely a bound on
  `|S_t + S_u|` better than `max(|S_t|, |S_u|)` for two `4`-caps, which is a finite but real
  case analysis (a `4`-cap in `F₃²` is a frame, and the sumset of two frames is large).
* `f(4) ≤ 20` would then give `20 · 3^{n-4} = (20/81)·3ⁿ`, and `f(5) ≤ 45`, `f(6) ≤ 112` more
  still, but those are computer results and out of reach of a budgeted kernel proof.

Brute force is not an option at any of these: `decide` over
`powersetCard k (univ : Finset (Fin n → ZMod 3))` is exactly the kind of kernel search the
computation budget forbids (and `f 3 = 9` by `decide` would be `2^27` subsets).

**Problems hit.** Only small ones. `omega` does not see `3 ^ n` as a nonnegative atom in one
`ℕ`-subtraction goal (`(3ⁿ−1)/2 ≤ (3ⁿ+1)/2` in V002's `improves`), so that step goes through
`Nat.div_le_div_right` by hand. Names clash between V001's `mem_slice` and `Finset.mem_slice`
once `Finset` is open, so V002 qualifies it. Both records stay far inside the heartbeat budget
(≈ 13.5k of 200000 each) because nothing is computed: the only `decide`s are on `ZMod 3`.

## State after V008 — `trial claude-fable`

**Where the record stands.** `record n = min(3^(n-1), EG(n), H(n))`: exact at `n ≤ 4`;
`H(n)` (hyperplane recursion from `f 4 = 20`, `≈ 3ⁿ/n`) binds for `5 ≤ n ≤ 30`; the
Ellenberg–Gijswijt value `EG(n)` binds from `n = 31` on. Feeding `EG(n-1)` back into the
recursion never beats `EG(n)` (checked to `n = 100`), and the asymmetric degree split in the
Ellenberg–Gijswijt rank bound never beats the symmetric one (checked to `n = 60`), so the two
methods are combined optimally.

**What is left, in order of value.**

* **Better base values for the recursion.** The literature chain from `f 6 = 112` is
  `292, 773, 2075, 5632, …` against our `312, 820, 2187, 5905, …`: about 7% at every
  `5 ≤ n ≤ 30`. But `f 5 = 45` (Edel–Ferret–Landjev–Storme 2002) and `f 6 = 112`
  (Potechin 2008) rest on computer classifications. The moment identities used here cannot
  exclude a `46`-, `47`- or `48`-cap in `F₃⁵`: with about two hundred admissible section
  types and only four constraints (first to third moments and the plane-counting fourth
  moment, which only gives an interval) the corresponding linear program is feasible;
  `48` is not an equality case of the recursion, so the parity trick of `n = 4` does not
  apply. Davis–Maclagan's route to `45` (Prop. 9: a `46`-cap must have a `19`- or
  `20`-point hyperplane section) needs the structure of `19`- and `20`-caps in `AG(4,3)`.
* **A better recursion.** The Bierbrauer–Edel step is `c_n ≤ c_{n-1}/(1 + c_{n-1})` up to
  `3^{-n}`, the same density increment `α ↦ α + α²` that Fourier analysis gives; Meshulam's
  `2·3ⁿ/n` is weaker only because of lossy iteration. Beating `3ⁿ/n` by a constant factor
  would need a stronger increment, i.e. Bateman–Katz-type structure — out of reach.
* **Beyond `n = 30`.** Ellenberg–Gijswijt's exponent `2.7551` is the best known and is
  tight for the polynomial method; only the polynomial factor could move, and the minimum
  over `d` already takes the best of it.

**Problems hit.** (1) The first V007 evaluated `m_n(d)` by a list recurrence and cost
`> 200000` heartbeats from `n = 59` on once the verifier evaluated the record at every
`n ≤ 100`: kernel evaluation does not share lazily evaluated list elements. Big-number
digit extraction (`(1 + B + B²)ⁿ` in base `B = 3ⁿ + 1`) costs under 100 heartbeats at
`n = 100`. Rule of thumb: a record should be a short chain of `Nat` operations on numerals;
recursion over `n` with a numeral accumulator (`chain` in V008, `msum` in V007) is fine.
(2) `omega` treats `f (0 + 4)` and `f 4`, or `3 ^ (m + 2)` and `9 * 3 ^ m`, as different
atoms; normalise with `show` or an explicit `ring` identity first. (3) A local lemma named
`card_pair` shadowed `Finset.card_pair`. (4) `Finset.sum_nonneg` needs the summation set
given explicitly when the summand is a lambda. (5) Comparator/`squeeze verify` take about
five minutes per run; scratch files under `lake env lean` iterate in about a minute.

**Scratch prototypes** (relative to the project root, in the session scratch directory
`.lake/scratch/CapSet-Upper/`): `EG1.lean` (Ellenberg–Gijswijt core), `EG2.lean` (counting
recurrence, no longer used), `Digit.lean` and `GenFun.lean` (digit extraction and the generating
function of V007), `Cand.lean` / `Cand2.lean` (kernel-cost probes of the V007 and V008 records),
`BE1.lean` (the whole V008 development, including `cap_four`). The withdrawn first V007 is kept
in `withdrawn/V007/` there. All accepted work is in the record directories; nothing is
unfinished.
