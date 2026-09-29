# ExC4 — upper track report

`f(n) = ex(n; C₄)`, the largest number of edges of a `C₄`-free simple graph on `n` vertices
(OEIS A006855). `nMin = 1`.

## Literature: best known upper bounds

- **Kővári–Sós–Turán (1954)**, *On a problem of K. Zarankiewicz*, Colloq. Math. 3, 50–57.
  The first `O(n^{3/2})` bound; for `C₄` it gives `f(n) ≤ ½ n^{3/2} + O(n)`.
- **Reiman (1958)**, *Über ein Problem von K. Zarankiewicz*, Acta Math. Acad. Sci. Hungar. 9,
  269–273. The sharp form of the cherry count:
  `f(n) ≤ ¼ · n · (1 + √(4n − 3))`.
  This is still the best *general* closed-form upper bound in the literature.
- **Erdős–Rényi–Sós (1966)** and independently **Brown (1966)**: the polarity graph `ER_q` of the
  projective plane `PG(2,q)` is `C₄`-free with `½ q(q+1)²` edges on `q² + q + 1` vertices, so
  `f(n) ~ ½ n^{3/2}`. Reiman's bound exceeds this construction by exactly `(q+1)/2`
  (the absolute points of the polarity), so it is asymptotically but not exactly tight.
- **Füredi (1996)**, *On the number of edges of quadrilateral-free graphs*, JCTB 68, 1–6:
  `f(q² + q + 1) = ½ q(q+1)²` for every prime power `q > 13`, i.e. the polarity graph is optimal
  at those orders.
- **Firke–Kosek–Nash–Williford (2013)**, *Extremal graphs without 4-cycles*, JCTB 103, 327–336:
  `f(q² + q) ≤ ½ q(q+1)² − q` for every even `q`, with equality when an orthogonal polarity graph
  of order `q` exists (the earlier entry here misquoted this as a bound at `q² + q + 2`). The key
  lemma bounds `Σ_v C(d(v), 2)` by `qm − n_{q+1} + ½ n_{q+2}` through the vertices missed by
  2-paths, with the parity obstruction at degree `q + 1`.
- **Ma–Yang (2023+)** disproved the conjecture `f(n) = ½ n^{3/2} + n/4 + O(√n)`, so the correct
  linear term is open.
- **Füredi (1983)**, *Graphs without quadrilaterals*, JCTB 34, 187–190. Proves
  `f(q² + q + 1) ≤ ½ q(q+1)²` for every even `q` by an elementary argument: a *restricted cherry
  count* around a vertex of maximum degree excludes degrees `≥ q + 2`, and the parity of the
  matching inside a neighbourhood then forces at least `q + 1` vertices of degree `≤ q`. The
  restricted count is the bound of V004 below.
- **Ma–Yang (2023)**, *Upper bounds on the extremal number of the 4-cycle*, Bull. LMS 55,
  1655–1667: `f(q² + q + 1 − r) ≤ ½ q(q+1)² − 0.92 rq` for large `q` and `r ≤ 0.01 q`, and
  `f(q² + q + 1 + r) ≤ ½ (q² + q + 1 + max(r, 2r − 0.3q))(q + 1)` for `1 ≤ r ≤ 0.6 q`; hence
  `f(n) ≤ ½ n^{3/2} + (¼ − ε) n` on a set of positive density, which disproves the conjectured
  `½ n^{3/2} + n/4 + O(√n)`.
- **Wu–Sun–Zhang–Radziszowski (2015)**, *Ramsey numbers of C₄ versus wheels and stars*, Graphs
  Combin. 31, 2437–2446: `f(q² + q + 2) < ½ (q+1)(q² + q + 2)` for `q` even or an odd prime power.
- **He–Ma–Yang (2023)**, *Some exact results on 4-cycles: stability and supersaturation*, CSIAM
  Trans. Appl. Math. 4, 74–128: stability — for large even `q`, a `C₄`-free graph on `q² + q + 1`
  vertices with at least `½ q(q+1)² − (½ − η) q` edges lies inside a polarity graph.
- **Bondy–Erdős–Fajtlowicz (1999)**, *Graphs of diameter two with no 4-circuits*, Discrete Math.
  200, 21–25: such graphs are polarity graphs, Moore graphs, or have a dominating vertex. Relevant
  because the slack of the cherry count is exactly the number of pairs at distance `≥ 3` plus the
  edges in no triangle.
- Exact values are known for `n ≤ 40` (Clapham–Flockhart–Sheehan 1989 for `n ≤ 21`,
  Yang–Rowlinson 1992 for `22 ≤ n ≤ 31`, Shao–Xu–Xu for `n = 32`, McKay for `33 ≤ n ≤ 40`);
  from `n = 41` only `132 ≤ f(41) ≤ 133` is known. These rest on computer searches that cannot
  be replayed inside the heartbeat budget, so they are not a route to a record here.

Starting record of this track: `V000`, the ambient bound `C(n, 2)`.

## V001 — `baseline claude-opus-5`

**Bound.** `record n = min( C(n,2), ⌊(n + ⌊√(n²(4n−3))⌋) / 4⌋ )`, i.e. Reiman's
`¼ n (1 + √(4n−3))` rounded down, folded into the previous record by `minWith`.
This drops the record from order `n²` to order `n^{3/2}` at every `n ≥ 6`.

**Idea of the proof.**

1. *Cherry count.* For a `C₄`-free `G`, two distinct vertices have at most one common
   neighbour, so the families `{S ⊆ N(x) : |S| = 2}` are pairwise disjoint as `x` ranges over
   the vertices, and all lie inside the 2-subsets of the vertex set. Hence
   `Σ_x C(d(x), 2) ≤ C(n, 2)` (`sum_choose_degree_le`, via `Finset.card_biUnion`).
2. *Sum of squares.* `d² = 2·C(d,2) + d` (`mul_self_eq`), so with `Σ_x d(x) = 2m`
   (handshake) one gets `Σ_x d(x)² ≤ n(n−1) + 2m`.
3. *Cauchy–Schwarz.* Mathlib's `sq_sum_le_card_mul_sum_sq` gives `(2m)² ≤ n · Σ_x d(x)²`, hence
   `4m² ≤ n²(n−1) + 2mn`.
4. *Completing the square.* That is `(4m − n)² ≤ n²(4n−3)`, so `4m ≤ n + √(n²(4n−3))`
   (`reiman_arith`, using `Nat.le_sqrt`).

**Why this shape of record.** `Nat.sqrt` does not reduce in the kernel at the sizes needed, so
`Def.lean` carries its own integer square root `isqrt`: 64 Newton steps
`g ↦ min g ⌊(g + x/g)/2⌋` from `g₀ = x+1`, written as a plain structurally-recursive `def`, which
the kernel evaluates cheaply. Only one direction of correctness is needed for validity —
`Nat.sqrt x ≤ isqrt x`, proved from the AM-GM step lemma `sqrt_le_sqrtStep` — so even if the
fuel ran out the record would stay valid; in fact `isqrt = Nat.sqrt` far beyond any `n` of
interest.

**Witness.** `n₀ = 10`: `45 → 17` (true value `f(10) = 16`).

**Budget.** 48217 heartbeats in all (limit 200000); heaviest declaration `reiman_arith`, 13794.

## V002 — `baseline claude-opus-5`

**Bound.** `record n = V001.record n − [ ¬cherryOk(n, 2·V001.record n) ]`, i.e. Reiman's value
lowered by one edge at every `n` where it is incompatible with an *integral* degree sequence.
Here, with `q = ⌊S/n⌋`,

```
cherryOk(n, S)  :⇔  n·C(q,2) + q·S  ≤  C(n,2) + n·q²
```

which is the subtraction-free form of `n·C(q,2) + q·(S − qn) ≤ C(n,2)`.

**Idea of the proof.** Reiman's bound applies Jensen to *real* degrees. For integers, the tangent
line to `C(·,2)` at `q` is an inequality in ℕ,

```
C(q,2) + q·d  ≤  C(d,2) + q²        (tangent)
```

— it is `(d−q)² ≥ d−q`, true for integers — proved here from the Vandermonde identity
`C(m+c,2) = C(m,2) + mc + C(c,2)`. Summing it over the vertices and inserting the handshake
`Σ_x d(x) = 2m` and V001's cherry count `Σ_x C(d(x),2) ≤ C(n,2)` gives exactly
`cherryOk(n, 2m)` for every `C₄`-free graph. So if `cherryOk(n, 2·u)` fails at `u = V001.record n`,
no `C₄`-free graph attains `u` edges and the record drops by one. Validity therefore reuses
V001 wholesale: `m ≤ u` comes from `V001.valid`, and `m ≠ u` from the failing test.

**Why this bound.** It improves the record at 69 of the first 200 values of `n`
(`n = 15, 28, 35, 46, 52, 62, 63, 66, 67, 69, 78, …`, and every `n` in long runs such as
`78 ≤ n ≤ 85` and `103 ≤ n ≤ 108`), so it is an improvement at a large set of `n`, not at a
point. It is also the only step available that needs no new graph theory, only integrality.

**Witness.** `n₀ = 15`: `32 → 31` (true value `f(15) = 30`).

**Budget.** 9974 heartbeats in all (limit 200000). The record function avoids `Nat.choose`
(whose kernel reduction is quadratic in `n`) in favour of `c2 a = a(a−1)/2`, so evaluating it at
large `n` stays one division per term.

## V003 — `baseline claude-opus-5`

**Bound.** With `q` an odd integer,

```
record n  =  min( V002.record n,  min over q ∈ {q₀, q₀+2} of  ⌊ ⌊(n(n−1) + n·q² − n) / (2q−1)⌋ / 2 ⌋ )
```

where `q₀ = 2·⌊⌊2·V002.record n / n⌋/2⌋ + 1` is the odd level nearest the average degree V002
still allows. It improves V002 at **1858 of the first 2000 values of `n`**, by up to 9 edges in
that range.

**Idea of the proof.** The new inequality is a *triangle-corrected* cherry count. Write
`d(v)` for degrees, `m` for the number of edges.

1. *A vertex `v` may be added to the count.* For every vertex `v` collect the ordered pairs
   `(x,y)` of distinct neighbours of `v` (there are `d(v)² − d(v)` of them), **and** the pairs
   `(v,x)` for those neighbours `x` that share no neighbour with `v` (call the other neighbours
   `M(v)`; there are `d(v) − |M(v)|` of them). All these finsets, over all `v`, are pairwise
   disjoint subsets of the `n(n−1)` ordered pairs of distinct vertices: two pairs of neighbours
   collide only if two vertices have two common neighbours, and `(v,x)` is in nobody else's
   list precisely because `x ∉ M(v)`. Hence

   ```
   Σ_v ( d(v)² − |M(v)| )  ≤  n(n−1).
   ```

2. *`|M(v)|` is even.* The edges inside `N(v)` form a matching — a vertex with two neighbours in
   `N(v)` would give `v` and that vertex two common neighbours — so the ordered pairs of adjacent
   neighbours of `v` project injectively onto `M(v)`, and they split into the pairs with
   `x < y` and their swaps. So `|M(v)| = 2t` with `2t ≤ d(v)`, i.e. `|M(v)| ≤ 2⌊d(v)/2⌋`. This is
   where the gain comes from: a vertex of odd degree always has a neighbour sharing nothing
   with it.

3. Therefore `Σ_v ψ(d(v)) ≤ n(n−1)` with `ψ(d) = d² − 2⌊d/2⌋ = d² − d + (d mod 2)` — Reiman's
   cherry count plus one for every odd degree.

4. *Tangent at an odd level.* `ψ` is convex, and at an **odd** `q` the tangent of slope `2q−1`
   is the clean statement `1 + 2qd ≤ d² + q² + (d mod 2)`, i.e. `(d−q)² + (d mod 2) ≥ 1`: true
   because `d ≠ q` gives `(d−q)² ≥ 1` and `d = q` gives `d mod 2 = 1`. Summing it over the
   vertices with `Σ_v d(v) = 2m` and step 3 gives `(2q−1)·2m + n ≤ n(n−1) + n·q²`, which is the
   record after two divisions.

**Why this bound.** Unlike V002's single-edge integrality correction it improves the record at
almost every `n` (93% of the first 2000), and it is the first submission here that uses graph
structure beyond the cherry count. Restricting the tangent point to *odd* `q` costs nothing
numerically — the min over `{q₀, q₀+2}` reproduces the exact discrete optimum of
`max Σd subject to Σψ(d) ≤ n(n−1)` at every `n ≤ 1000` — and it makes the tangent lemma a
one-line inequality.

**Witness.** `n₀ = 6`: `8 → 7` (true value `f(6) = 7`, so the bound is tight there).

**Budget.** 23283 heartbeats in all (limit 200000); heaviest declarations `tangent` 7039,
`key` 3723, `uset_card` 2999.

## V004 — `trial claude-fable`

**Bound.** With `p = max(1, ⌊2·V003(n)/n⌋ − 1)`,

```
bp(n, d, p)  =  ⌊ (2pd + (n−1)p(p+3) + (n−d)(n−d−1)) / (4p) ⌋
record n     =  min( V003(n),  max over d < n of  min(⌊nd/2⌋, bp(n, d, p)) )
```

It improves V003 at **1467 of the first 2000 values of `n`**, by up to 12 edges
(`n = 27: 75 → 74`, `n = 100: 521 → 520`, `n = 1000: 16053 → 16041`).

**Idea of the proof** (Füredi 1983, first step). Let `x` be a vertex of maximum degree `d`,
`S` the set of the `n − d` vertices that are not neighbours of `x` (`x` included), and `a_v` the
number of neighbours of `v` inside `S`.

1. *Restricted cherry count.* The ordered pairs of distinct neighbours of `v` inside `S`, over
   all `v`, are pairwise disjoint subsets of `S × S` minus its diagonal (a pair in two of them is
   a pair with two common neighbours), so `Σ_v a_v(a_v − 1) ≤ (n − d)(n − d − 1)`
   (`sum_aset_le`).
2. *Every `v ≠ x` has at most one neighbour in `N(x)`* (two would be two common neighbours of
   `v` and `x`), so `a_v ≥ d(v) − 1` (`degree_le_aset`).
3. *Chord.* `2pa ≤ a(a − 1) + p(p + 1)` for all integers `a`, i.e. `(a − p)² ≥ a − p`
   (`chord`), tight at `a ∈ {p, p+1}`. Summing over `v ≠ x` and using the handshake
   `Σ_{v ≠ x} d(v) = 2m − d` gives `4pm ≤ 2pd + (n − 1)p(p + 3) + (n − d)(n − d − 1)` (`key`).
4. *Maximum degree.* `2m ≤ nd`. The record scans every possible maximum degree `d < n` and
   takes the largest candidate `min(⌊nd/2⌋, bp)`; the proof only needs that the actual maximum
   degree is one of them (`cand_le_scanMax`), so no monotonicity is proved.

**Why this bound.** Deleting the `d` neighbours of `x` from the cherry count costs the count
`≈ 2dn` but the degree sum only `d`, so the bound beats Reiman's exactly when an integral maximum
degree is forced above the real average degree — which happens at about three quarters of all
`n`. The candidates cross at `d = ⌈2m/n⌉`. The chord level `p = ⌊2·V003(n)/n⌋ − 1` was checked
against the best `p` in Python for every `n ≤ 600` and loses nothing. The record is cheap: the
scan is `n` evaluations of a fixed polynomial expression (443 heartbeats at `n = 100`, about
22000 at `n = 1000`).

This bound came out of a numerical study of linear programs over degree classes (below); the
consultation tool pointed to Füredi's paper for the restricted count, which is as strong as the
per-vertex LP at many `n`, beats it at some, and has a proof of the same shape as V001 and V003.

**Witness.** `n₀ = 27`: `75 → 74` (true value `f(27) = 71`).

**Budget.** 15713 heartbeats in all (limit 200000); heaviest declarations `chord` 4059,
`key` 3309, `v_valid` 2459.

## V005 — `trial claude-fable`

**Bound.** A *weighted local count*, certified per `n` by a table in `Def.lean`. For every
vertex `x` of a `C₄`-free graph, with `s(x) = Σ_{y ∈ N(x)} (d(y) − 1)`,

```
s(x) + (d(x) mod 2)  ≤  n − 1                                              (L)
```

(the sets `N(y) \ {x}`, `y ∈ N(x)`, are pairwise disjoint, disjoint from the neighbours of `x`
that share no neighbour with `x`, and lie among the other `n − 1` vertices; an odd-degree
vertex has such a lone neighbour by V003's matching argument). V003 sums (L) over all
vertices; V005 sums it with a weight `w(d(x))` depending on the degree. A certificate for `n`
is `(k, ls, B)`: weights `w(i)` (scaled by `M = 2²⁰`: `0` for `i < k`, the list `ls` from `k`
on, a tail `g = ⌊β/(n−1)⌋` beyond it, with `β = ⌊(2M(B+1) − 1)/n⌋`) and offsets `δ(i)`
computed from them. The record checks the finitely many inequalities

```
(D1)  M·i + w(i)(n − 1 − (i mod 2)) + i·δ(i)  ≤  β + i·w(i)(i − 1)          (i < T)
(D2)  w(i)(i − 1) + w(j)(j − 1)  ≤  w(i)(j − 1) + w(j)(i − 1) + δ(i) + δ(j)  (i < j ≤ T)
```

plus two tail conditions, and returns `B` if they pass, else V004; `record = min(V004, ·)`.

**Idea of the proof.** (D2) summed over the ordered adjacent pairs and regrouped by vertices
gives `Σ_x d(x)·w(d(x))(d(x)−1) ≤ Σ_x w(d(x))·s(x) + Σ_x d(x)·δ(d(x))`; (L) bounds `s(x)`;
(D1) summed over the vertices with the handshake gives `2Mm ≤ nβ < 2M(B+1)`. This is LP
duality for the linear program over degree classes (numbers of vertices per degree, numbers
of edges per pair of degrees, the sum of (L) per class), with the offsets chosen as large as
(D1) allows so that only the weights are data. The tail formulas extend (D1)/(D2) from the
checked range to all degrees (`d1_all`, `d2_all`).

**Why this bound.** The class LP beats V004 at about 55% of `n ≤ 300` and its optimal dual
has no closed form (the set of tight constraints changes more than fifty times below
`n = 200`), so the record carries the data and the proof is general. The table holds the 944
values `n ≤ 1240` at which the certificate beats V004 (735 of the first 1000), gains of up to
22 edges (`n = 1106`), 7247 edges in all: `n = 15: 31 → 30` (the true value),
`n = 18: 41 → 40`, `n = 200: 1458 → 1455`, `n = 1000: 16041 → 16035`. The certificates were
found by SciPy/HiGHS (LP restricted to the certificate's shape, then maximal slack at the
target, rounding to `1/M`, exact re-check); the shape with five free levels matches the
unrestricted LP's floor at 99 of the 101 values `n ≤ 130`.

**Witness.** `n₀ = 15`: `31 → 30` (true value `f(15) = 30`).

**Budget.** 23110 heartbeats in all (limit 200000); heaviest declarations `d2_all` 4967,
`key` 4332, `local_ineq` 4216. Evaluating the record costs about 2000 heartbeats at
`n = 100` and 24000 at `n = 1000`. `Def.lean` is 51 KB (limit 64 KB).

## Values

| n | 5 | 6 | 10 | 13 | 15 | 20 | 27 | 28 | 40 | 100 | 1000 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| `f(n)` (known, A006855) | 6 | 7 | 16 | 24 | 30 | 46 | 71 | 76 | 127 | ? | ? |
| V000 `C(n,2)` | 10 | 15 | 45 | 78 | 105 | 190 | 351 | 378 | 780 | 4950 | 499500 |
| V001 (Reiman) | 6 | 8 | 17 | 26 | 32 | 48 | 75 | 80 | 135 | 523 | 16055 |
| V002 (integral degrees) | 6 | 8 | 17 | 26 | 31 | 48 | 75 | 79 | 135 | 522 | 16054 |
| V003 (odd-degree correction) | 6 | **7** | 17 | 26 | 31 | **47** | 75 | 79 | **133** | **521** | 16053 |
| V004 (restricted cherry count) | 6 | 7 | 17 | 26 | 31 | 47 | **74** | 79 | 133 | **520** | **16041** |
| V005 (weighted local count, certified) | 6 | 7 | 17 | 26 | **30** | 47 | 74 | **78** | 133 | 520 | **16035** |

## Unfinished: V006 (parked, not accepted) — `trial claude-fable`

The directory `SqueezeBench/Problems/ExC4/Records/Upper/V006/` holds a scaffolded, **unaccepted**
version (the Challenge `Challenges/ExC4/Upper/V006.lean` is open). It combines V005's weighted
local count with V004's restricted cherry count, both applied to the vertex `x` of maximum
degree `d`, with one certificate per `(n, d)`:

- **Bound.** For a graph of maximum degree `d`, with weights `w(i)` for `i ≤ d` (no tail: the
  degree cap makes (D1)/(D2) finite), a multiplier `l ≥ 0` for the restricted count
  `Σ_{v ≠ x} (d(v)−1)(d(v)−2) ≤ (n−d)(n−d−1)`, and the offsets `δ(i)` computed as the largest
  allowed by `(D1') M·i + w(i)(n−1−(i mod 2)) + i·δ(i) ≤ β + i·w(i)(i−1) + l(i−1)(i−2)`,
  one gets `2Mm ≤ nβ + l(n−d)(n−d−1) + excess`, where `excess` is what `x` itself exceeds the
  plain (D1) by (computed, not checked). The record scans `d < n` like V004, taking
  `min(V004's candidate, fbound)` when a certificate for `(n, d)` passes `certOk`, and
  `record = min(V005, ·)`. Only the one or two values of `d` at the crossover need a
  certificate; for the others V004's candidate already suffices.
- **Numbers.** The class LP with the restricted count and the degree cap ("joint LP",
  `jointlp.py`) beats V005 at 853 of the first 1240 values of `n` (688 of the first 1000),
  by up to 10 edges, 2419 edges in all; small cases: `n = 16: 34 → 33`, `20: 47 → 46`,
  `21: 51 → 50` (all three the true values), `39: 128 → 127`, `41: 138 → 136`. The generator
  `gen7.py` (scratch directory `work/`) found and exactly verified certificates for all of
  them; they are in `table7_<lo>_<hi>.txt` and assembled into `V006/Def.lean` by `mkdef6.py`.
- **State of the files.** `Def.lean` builds, but with all 1162 certificates it is 121 KB,
  above the 64 KB limit: keep roughly `n ≤ 600` (or shorten the entries: `β` could be stored
  as an offset from `2M(B+1)/n`). `Proof.lean` is written in full (certificate lemmas
  `d1_all`, `d2_all`; `restricted` from V004's `sum_aset_le`/`degree_le_aset`; `key`;
  `edges_le_cand`; `v_valid`; witness `106`) and fails only at two `omega` calls in `key`
  (lines 138 and 188): the `let`-bound `w`/`δ` are not unfolded, so `omega` sees `w D` and
  `wt k ls D` as different atoms — replace the `let`s by `wt k ls` and `dlow n β l i (wt k ls i)`
  written out (or `simp only [w, δ]` before `omega`), and check the association of the four
  `Finset.sum_add_distrib` rewrites in `hsum`. Then `lake build`, pick a witness present in
  the trimmed table (`16` is the natural one: `34 → 33`), `squeeze verify`, `accept`, and
  write `V006/REPORT.md` (the template is untouched).

## What the next improvement would take

- **Finish V006** as above: about an hour of work, 853 more values of `n` (before trimming).
- **Sharper local counts.** Everything from V003 on rests on (L) `s(x) + (d(x) mod 2) ≤ n−1`
  and, since V004, on the restricted count around one vertex. Two elementary refinements
  were identified but not used: (i) the restricted count applied at *every* vertex `x` with
  weights (its sum over `x` gives nothing new, but weighting by degree class might, exactly as
  (L) gained over its plain sum); (ii) the exact identity
  `Σ_v d(v)(d(v)−1) + 2E₀ + B = n(n−1)` with `E₀` the edges in no triangle and `B` the ordered
  pairs at distance `≥ 3`, together with `E₀ ≡ m (mod 3)` (`3T = m − E₀`), which the
  consultation suggested as a cheap congruence test on the degree sequence (only a `−1`
  at isolated `n`).
- **Füredi's even-order theorem** `f(q²+q+1) ≤ ½q(q+1)²` for even `q` follows from V004's
  count (it excludes degree `≥ q+2`) plus a parity argument (each degree-`(q+1)` vertex needs
  a neighbour of degree `≤ q`); the joint LP already reproduces it numerically at
  `n = 21, 73` (V006 gives `50` and `324`), so it comes for free from V006's certificates
  where they exist, and a closed-form version would extend it to all even `q`.
- **Beyond** lies Ma–Yang's method (degree deficiencies, restricted 2-path counts, weighted
  counting), which gives `f(n) ≤ ½n^{3/2} + (¼ − ε)n` on a set of positive density; it is a
  more elaborate weighting of the same local counts and might be expressible as certificates
  of the V005/V006 kind with more constraint families.
- **Limits of the table approach.** A closed form for the certificates was not found (the LP's
  tight-constraint pattern changes more than fifty times below `n = 200`), so V005 and V006
  improve at a large finite set of `n`. A formula would need the LP solved symbolically per
  pattern; a cheaper route is a table of *coarser* certificates (fewer digits, `M = 2¹⁶`)
  covering more `n` within the 64 KB limit.

## What the next improvement would take (as written after V003 by baseline claude-opus-5)

- **Iterate the integrality test.** V002 lowers the Reiman value by *one* when the test fails.
  Descending until the test passes was measured: for every `n ≤ 300` the descent stops after
  exactly one step, so this route gains nothing. Likewise the vertex-deletion recursion
  `m ≤ record(n−1) + ⌊2m/n⌋` was measured and gains nothing up to `n = 400` — Reiman's bound is
  self-consistent under deleting a minimum-degree vertex.
- **Sharpen step 2 of V003.** `|M(v)| ≤ 2⌊d(v)/2⌋` is what a *perfect* matching inside `N(v)`
  would give. A vertex whose neighbourhood carries a perfect matching has `d(v)/2` triangles
  through it; bounding the total number of triangles globally (each edge lies in at most one)
  would push `ψ` further up and is elementary — the obstacle is that the bound `3T ≤ m` is
  already implied by what V003 uses, so a genuinely new count of triangle-free edges is needed.
- **Parity.** `Σ_x d(x) = 2m` is even, and a `C₄`-free graph with `n·C(q,2) + q·r` exactly equal
  to `C(n,2)` must have every pair of vertices with exactly one common neighbour, which by the
  friendship theorem forces a windmill — never `q`-regular for `q ≥ 3`. Formalising the
  friendship theorem is out of reach here, but the equality case at `r = 0` (a `q`-regular graph
  in which every pair has exactly one common neighbour) might be excluded by a short counting
  argument and would shave another edge at the orders `n ≡ 1 (mod q)`.
- **Beyond that** the literature offers nothing closed-form better than Reiman for general `n`.
  Füredi's exact result at `n = q²+q+1` and Firke–Kosek–Nash–Williford at `n = q²+q+2` would
  each need the projective plane and a polarity argument in Lean, plus a primality/prime-power
  test in the record function — a much larger job. A cheaper partial gain: the
  absolute-point deficit `(q+1)/2` at `n = q²+q+1` is exactly the gap between Reiman and the
  truth, and a "no graph is `(q+1)`-regular with every pair having exactly one common
  neighbour" argument would recover part of it.

## Scratch files

All in the session scratch directory `.lake/scratch/ExC4-Upper/work/` (persists between
sessions): `records.py` (Python replicas of V001–V003), `v004.py` (V004 replica),
`classlp.py`/`jointlp.py` (the LPs), `fured.py` (restricted count), `gen.py` (V005
certificates, output `table_*.txt`, `table_all.txt`), `gen7.py` + `mkdef6.py` (V006), and a
virtual environment `venv/` with SciPy.
