# RuzsaSzemeredi — upper track

`f n` = largest number of **triangles** in a locally linear graph on `n` vertices (every edge
lies in exactly one triangle). `nMin = 3`.

Submitters of the versions below: `baseline claude-opus-5` (V001–V005) and `trial claude-fable`
(V006–V008).

## What the literature says

* **Asymptotics.** Ruzsa and Szemerédi's (6,3)-theorem says a locally linear graph on `n`
  vertices has `o(n²)` edges, hence `f n = o(n²)`; the proof goes through the triangle removal
  lemma (I. Z. Ruzsa, E. Szemerédi, *Triple systems with no six points carrying three
  triangles*, Colloq. Math. Soc. János Bolyai 18 (1978), 939–945). The best quantitative
  upper bound is Fox's proof of the removal lemma (J. Fox, *A new proof of the graph removal
  lemma*, Ann. of Math. 174 (2011), 561–579), which only saves an inverse-tower-type factor
  over `n²`: nothing of that shape is within formalisation reach, and it beats the elementary
  bound only for astronomically large `n`.
* **Lower side, for contrast.** Behrend's 3AP-free sets give `f n ≥ n²/e^{O(√log n)}`
  (F. A. Behrend, PNAS 32 (1946), 331–332, via the Ruzsa–Szemerédi construction — this is
  `ruzsaSzemerediNumberNat_asymptotic_lower_bound` in Mathlib). So the truth is `n^{2-o(1)}`
  and the elementary quadratic upper bounds below are the right order of magnitude up to
  `n^{o(1)}`.
* **Elementary bounds, which is what is formalisable.** The triangles of a locally linear
  graph are pairwise edge-disjoint, so they form a *partial Steiner triple system*: any two
  vertices lie in at most one triangle. Hence `f n ≤ D(n,3,2)`, the packing number of triples,
  which is exactly `⌊n/3·⌊(n-1)/2⌋⌋`, minus `1` when `n ≡ 5 (mod 6)` (Spencer's completion of
  the Schönheim bound; J. Spencer, *Maximal consistent families of triples*, J. Combin.
  Theory 5 (1968), 1–8). The three ingredients are: `3·T ≤ #edges`, `#edges ≤ C(n,2)`, and
  per vertex `2·(triangles at v) ≤ deg v`.
* **Small values** (from the problem README, computed there by exhaustive search; reporting
  only, never a source of theorems): `f(3..13) = 1, 1, 2, 2, 3, 4, 6, 6, 7, 9, 10`. These
  fall well below the packing bound, since a partial Steiner system whose union graph has
  *extra* triangles is not locally linear.

* **Additions by `trial claude-fable`.**
  - The bound `#edges ≤ n(n+3)/6`, i.e. V005's `T ≤ n(n+3)/18`, is published: D. Fronček,
    *Locally linear graphs*, Math. Slovaca 39 (1989), 3–6, Theorem 5 (pointed out by a GPT
    consultation; the proof there is the same degree-sum-along-a-triangle argument).
  - **Where `n(n+3)/18` is attained.** Equality forces a regular graph in which every vertex
    off a triangle is adjacent to exactly one of its vertices, i.e. the collinearity graph of a
    generalized quadrangle `GQ(2, t−1)` with `t = (n+3)/6` triangles per vertex. `GQ(2,t)` exists
    only for `t ∈ {1, 2, 4}` (Payne–Thas, *Finite Generalized Quadrangles*, §6.1), so the bound
    is tight exactly at `n = 9` (the 3×3 rook's graph, `T = 6`), `n = 15` (`GQ(2,2)`, the
    complement of the triangular graph `T(6)`, `T = 15`) and `n = 27` (`GQ(2,4)`, the complement
    of the Schläfli graph, `T = 45`). Hence `f(15) = 15`, `f(27) = 45`, and no bound `c·n²` with
    `c < 1/18` holds at every `n`. Deleting a point with its lines gives `f(14) ≥ 12` and
    `f(26) ≥ 40`, which meet the even-`n` bound of V006, so `f(14) = 12` and `f(26) = 40`.
  - **A triangle-free `16₃` configuration does not exist** (A. Al-Azemi, A. Betten, *Classification
    of triangle-free 22₃ configurations*, Int. J. Combin. 2010, Table 1: the numbers of
    triangle-free `v₃` configurations for `v = 15..22` are `1, 0, 1, 4, 14, 162, 4713, 157211`),
    so `f(16) = 15` (`16` triangles would force a `3`-regular configuration). Computer result,
    reporting only.
  - Z. R. Hassan, S. Radziszowski, S. Van Overberghe, *On small Folkman graphs arrowing K₂ or
    K₃*, arXiv:2605.16542 (2026), §3, report generating all locally linear graphs on up to 22
    vertices; the paper tabulates counts, not maximum triangle numbers.
  - **Induced matchings.** The `t_v` edges opposite `v` in its triangles form an induced matching,
    and these `n` matchings partition `E(G)`. J. Fox, H. Huang, B. Sudakov, *On graphs
    decomposable into induced matchings of linear sizes*, Bull. LMS 49 (2017), 45–57, Theorem
    1.2, bound such decompositions by a Plotkin-type double count; applied to all of `V` it is
    V003's `12T ≤ n(n+1)`, applied inside the common non-neighbourhood of a non-adjacent pair it
    is a genuinely new inequality (see *What the next improvement would take*).

## Starting record

`V000` (SqueezeBench): `record n = C(n,3)` — the ambient count of triples. Cubic, so it is
off by a factor of order `n`.

## V001 — `baseline claude-opus-5`

**Bound.** `record n = C(n,2) / 3` (natural division), i.e. `⌊n(n-1)/6⌋` for `n ≥ 1`.

**Idea.** In a locally linear graph the triangles are edge-disjoint, so `3·T ≤ #edges`
(Mathlib's `SimpleGraph.EdgeDisjointTriangles.card_edgeFinset_le`), and
`#edges ≤ C(n,2)` (`SimpleGraph.card_edgeFinset_le_card_choose_two`). Applying this to the
extremal graph handed over by `ruzsaSzemerediNumber_spec` gives `3·f n ≤ C(n,2)`.
`improves` is proved directly, not by `minWith`: `Nat.choose_succ_right_eq` gives
`C(n,3)·3 = C(n,2)·(n-2)`, so `C(n,2) ≤ 3·C(n,3)` for `n ≥ 3`, and `n ≤ 2` is a finite check.

**Why.** It turns a cubic bound into a quadratic one — the whole order of magnitude — and it
is the exact elementary bound for odd `n`.

**Witness.** `n₀ = 6`: `20 → 5`.

## V002 — `baseline claude-opus-5` (based on V001)

**Bound.** `record n = n · ⌊(n-1)/2⌋ / 3`, i.e. `⌊n(n-1)/6⌋` for odd `n` and `⌊n(n-2)/6⌋` for
even `n`. This is the packing bound `D(n,3,2)` without Spencer's `-1`.

**Idea.** Count incidences between triangles and vertices, with
`Finset.card_mul_le_card_mul` both times. Each triangle contains exactly `3` vertices. In the
other direction, the triangles through a fixed `v` meet `N(v)` in two vertices each
(`filter_neighbor_eq`: a triangle `t ∋ v` satisfies `N(v) ∩ t = t.erase v`), and two triangles
through `v` cannot share a neighbour `u`, since they would then both contain the edge `vu`
(`EdgeDisjointTriangles`). So `2 · #(triangles at v) ≤ deg v ≤ n - 1`, hence at most
`⌊(n-1)/2⌋` of them, and `3 · T ≤ n · ⌊(n-1)/2⌋`.

**Why.** It is the exact elementary packing bound, and it gains about `n/6` at every even `n`
— infinitely many — where V001 wastes the fact that a vertex of even `n` has degree at most
`n - 2` once degrees are paired up by the triangles.

**Witness.** `n₀ = 6`: `5 → 4`.

## V003 — `baseline claude-opus-5` (based on V001, V002)

**Bound.** `record n = ⌊n(n+1)/12⌋`. Asymptotically `n²/12`, half of the `n²/6` of V001–V002.

**Idea.** A locally linear graph has `#edges = 3·T`, so it is enough to bound `#edges`. The new
ingredient is a bound *along every edge*: if `u ~ v` then `N(u) ∩ N(v)` is a single vertex —
two common neighbours `a ≠ b` would give the two distinct triangles `{u,v,a}`, `{u,v,b}`
sharing the edge `uv`, against `EdgeDisjointTriangles` — hence
`deg u + deg v = #(N(u) ∪ N(v)) + #(N(u) ∩ N(v)) ≤ n + 1`.
Now take a vertex `v` of maximum degree `d` (`Finset.exists_max_image`). Its `d` neighbours
have degree at most `n + 1 - d`, and the other `n - d` vertices at most `d`, so
`2·#edges = Σ deg ≤ d(n+1-d) + (n-d)d = d(2n+1-2d)`. Over the integers
`d(2n+1-2d) ≤ n(n+1)/2` — the slack `(2d-n)(2d-n-1) ≥ 0` is a product of consecutive
integers, so this needs integrality of `d`; over the reals the maximum `(2n+1)²/8` is larger
by `1/8`. Hence `4·#edges ≤ n(n+1)` and `12·T ≤ n(n+1)`.

**Why.** It improves the constant of the leading term, so it gains a quadratic amount at every
`n ≥ 5` — the largest possible step short of the removal lemma, whose saving over `n²` is only
inverse-tower-type. The extra input over V002 is that local linearity restricts *pairs* of
adjacent vertices, not only single vertices: a vertex of large degree forces all its
neighbours to have small degree.

**Witness.** `n₀ = 5`: `3 → 2`.

## V004 — `baseline claude-opus-5` (based on V001, V002, V003)

**Bound.** `record n = n · 2⌊(n+1)/2⌋ / 12`, i.e. `⌊n(n+1)/12⌋` for odd `n` (as V003) and
`⌊n²/12⌋` for even `n`.

**Idea.** Every degree of a locally linear graph is **even**: the neighbours of `v` are paired
by the triangles through `v`, so `deg v = 2 · #(triangles at v)`. The `≤` half is V002's
incidence count (two triangles through `v` cannot share a neighbour); the `≥` half is the same
count with the two sides swapped — every neighbour `u` of `v` lies in at least one triangle
through `v` (local linearity applied to the edge `vu`), and each such triangle absorbs exactly
two neighbours. Hence `deg u + deg v` is even, so V003's bound `deg u + deg v ≤ n + 1` along an
edge sharpens to `deg u + deg v ≤ n` for even `n`. Feeding `M = n` into V003's maximum-degree
split (`2·#edges + d² ≤ d·M + (n-d)·d`) gives `4·#edges ≤ n²` — here the arithmetic needs only
`2cd ≤ c² + d²`, i.e. `(n-2d)² ≥ 0`, and not the consecutive-integers trick of V003.

**Why.** It gains `n/12` at every even `n`, strictly from `n = 8` on, and costs nothing at odd
`n`, where the record is unchanged. The degree-parity lemma is also the natural tool for any
later refinement.

**Witness.** `n₀ = 8`: `6 → 5`.

## V005 — `baseline claude-opus-5` (based on V001, V002, V003, V004)

**Bound.** `record n = ⌊n(n+3)/18⌋`. Asymptotically `n²/18`, two thirds of the `n²/12` of
V003–V004.

**Idea.** V003 bounded the degrees along an *edge*; V005 bounds them along a *triangle*. Let
`{u,v,w}` be a triangle, `A = N(u)`, `B = N(v)`, `C = N(w)`. Each pairwise intersection has at
most one element (V003's lemma: two common neighbours of an adjacent pair give two triangles on
the same edge), so from `|A ∪ B| + |A ∩ B| = |A| + |B|` and
`|(A∪B) ∪ C| + |(A∪B) ∩ C| = |A∪B| + |C|` together with
`(A∪B) ∩ C = (A∩C) ∪ (B∩C)`, whose card is at most `1 + 1 = 2`, and `|A∪B∪C| ≤ n`:

  `deg u + deg v + deg w ≤ n + 3` for every triangle.

Now run the whole count on the triangle counts `t_v`, using V004's `deg v = 2·t_v`. Double
counting triangle–vertex incidences with `Finset.sum_comm'`, once with weight `1` and once with
weight `deg`:

  `Σ_v t_v = 3T`  and  `2·Σ_v t_v² = Σ_v t_v·deg v = Σ_{triangles} Σ_{v ∈ t} deg v ≤ T(n+3)`.

Cauchy–Schwarz (`sq_sum_le_card_mul_sum_sq`, which applies over `ℕ`) gives
`(Σ t_v)² ≤ n·Σ t_v²`, i.e. `9T² ≤ n·Σ t_v²`. Combining, `18T² ≤ 2n·Σ t_v² ≤ n·T·(n+3)`, and
cancelling `T` (the case `T = 0` is trivial) leaves `18·T ≤ n(n+3)`.

**Why.** It lowers the constant of the leading term from `1/12` to `1/18`, so it gains a
quadratic amount at every `n ≥ 7` — the largest kind of step available short of the removal
lemma. The new input is that local linearity constrains *triples* of mutually adjacent
vertices, not only pairs: the third neighbourhood of a triangle overlaps the first two in only
two vertices in total. The bound is **tight at every small `n` where `f` is known from `7` on**:
`f(7)=3`, `f(8)=4`, `f(9)=6` all equal `⌊n(n+3)/18⌋` (the rook's graph `K₃□K₃` saturates it).

**Witness.** `n₀ = 7`: `4 → 3`.

## V006 — `trial claude-fable` (based on V001–V005)

**Bound.** `record n = n · (n + 2 + n % 2) / 18`, i.e. `⌊n(n+2)/18⌋` for even `n` and V005's
`⌊n(n+3)/18⌋` for odd `n`.

**Idea.** All degrees are even (V004), so the sum of the three degrees of a triangle is even
and V005's `deg u + deg v + deg w ≤ n + 3` sharpens to `≤ n + 2` when `n` is even: the three
neighbourhoods, of odd total size `deg u + deg v + deg w − 3`, then always miss a vertex.
V005's count with `n + 2` in place of `n + 3` gives `18T ≤ n(n+2)` for even `n`. V006 makes
the V002–V005 lemma library public (`trianglesAt`, `degree_eq`, `degree_sum_triangle_le'`,
`sum_card_trianglesAt`, `two_mul_sum_sq_le`, `exists_counts`) so later versions can import it.

**Why.** It gains about `n/18` at every even `n ≥ 10` (and at `n = 6`), and it is tight at every
even `n` where `f` is known: `f(6) = 2`, `f(8) = 4`, `f(10) = 6`, `f(12) = 9`, `f(14) = 12`,
`f(26) = 40`.

**Witness.** `n₀ = 10`: `7 → 6`.

## V007 — `trial claude-fable` (based on V001–V006)

**Bound.** `record n` = the largest `T ≤ V006.record n` passing the test `ok n T`. With
`c = 2 + n % 2`, `q = ⌊3T/n⌋`, `r = 3T mod n`, `cap t = min(2T + 2t, t(n+c) − 2t²)`:

    ok n T  ⟺  (n − r)·4q² + r·4(q+1)²  ≤  (n − r)·cap q + r·cap (q+1).

The record is a bounded downward search from V006's value (structural recursion); it stops
within a few steps at every `n ≤ 300`.

**Idea.** Let `s_v = Σ_{u ∈ N(v)} t_u`. Two bounds hold at every vertex: (A) `s_v ≤ T + t_v`,
because the triangles through `v` and, for each neighbour `u`, the `t_u − 1` triangles through
`u` avoiding `v` are pairwise distinct (a triangle avoiding `v` through two neighbours `u, u'`
would share the edge `uu'` with `{v, u, u'}`); and (B) `2s_v + 2t_v² ≤ t_v(n + c)`, V006's
triangle bound summed over the `t_v` triangles at `v`, whose pairs `τ \ {v}` partition `N(v)`.
Double counting gives `Σ_v s_v = 2Σ_v t_v²`, so `Σ_v g(t_v) ≤ 0` for the convex function
`g(t) = max(4t² − 2T − 2t, 6t² − (n+c)t)`. A convex function lies above the line through
`(q, g q)` with slope `g(q+1) − g q`, so over families with sum `qn + r` the most balanced one
minimises `Σ g(t_v)`, giving `(n−r) g(q) + r g(q+1) ≤ 0`, which is `ok n T`. Everything is
assembled in `ℤ`; `4t² − cap t ≤ g(t)` absorbs the truncated subtraction in `cap`.

**Why.** V005–V006 used (B) alone and Cauchy–Schwarz, tight only for regular graphs. Using (A)
at the vertices with the larger count and (B) at the others, together with the integrality of
the counts, gains `1` at `n = 13` (matching `f(13) = 10`), at `n = 18, 19, 23, 25, 29, 30, 31,
35, 36, 37, …`, and the gain grows like about `n/27` at `n ≡ 1, 5 (mod 6)` (`3` at `n = 67`,
`7` at `n = 193`, `10` at `n = 283`), with sporadic `1`s at even `n`. Nothing at
`n ≡ 3 (mod 6)`, where the bound is attained at `n = 9, 15, 27`.

**Witness.** `n₀ = 13`: `11 → 10`.

## V008 — `trial claude-fable` (based on V001–V007)

**Bound.** `record n` = the largest `T ≤ V007.record n` that the test `ok n T` cannot exclude.
The test adds a third per-vertex constraint to V007's two, and checks its own convexity
certificate. Definitions (`Records/Upper/V008/Def.lean`): `isqrt` (bisection, structural
recursion), `capAB t = V007.cap n T t / 2`, `capP t = ⌊(B + √(B² − 4AC)) / 2A⌋` with
`m = n − 1 − 2t`, `A = 4(m + t)`, `B = 2t(8t + 13m + m²)`,
`C = 16t³ + 30t²m + 4t²m² + tm² − tm³ + 6Ttm` (`0` if `B² < 4AC`),
`cap' t = min(capAB t, capP t)` when `1 ≤ t` and `2t + 1 < n`, else `capAB t`;
`ψ(t) = 4t² − 2·cap' t`; `ok n T` is true iff `(n − r) ψ(q) + r ψ(q+1) ≤ 0` **or** the chord
through `(q, ψ q)`, `(q+1, ψ(q+1))` exceeds `ψ` at some `t ≤ (n−1)/2` (`lineAbove`).

**Idea.** *Pair inequality.* For distinct non-adjacent `x, y` with `Z = N(x) ∩ N(y)`,
`c = |Z|`, `Y = V \ (N[x] ∪ N[y])` (so `|Y| = n − 2 − 2t_x − 2t_y + c`):
`2 Σ_{z ∈ Z} |N(z) ∩ Y| ≤ |Y| (c + 1)`. Proof: for `w ∈ Y` let `a_w = |N(w) ∩ Z|`; then
`Σ a_w = Σ_z |N(z) ∩ Y|` and `Σ a_w² = Σ_{z,z'} |N(z) ∩ N(z') ∩ Y|`; for `z ≠ z'` the pair
shares at most `t_z` neighbours in all (one per triangle at `z`), two of which are `x, y`, while
`|N(z) ∩ Y| ≥ 2t_z − 4` (the neighbours of `z` outside `Y` are `x`, `y` and the two triangle
partners), so `2|N(z) ∩ N(z') ∩ Y| ≤ |N(z) ∩ Y|`; Cauchy–Schwarz over `Y` finishes. This is the
Fox–Huang–Sudakov induced-matching count (Bull. LMS 49 (2017), Thm 1.2) run inside `Y`; it is
tight on `GQ(2,4)`, and in the regular case it gives `n ≥ 7t − 9`, i.e. `T ≤ n(n+9)/21`.
*Averaging* over the `m = n − 1 − 2t` non-neighbours `y` of a vertex `x` (`t = t_x ≥ 1`,
`m ≥ 1`), with `Σ_y c_y = 2s − 4t`, `c_y ≤ t_y`, `Σ_y t_y = 3T − t − s`, and Cauchy–Schwarz for
`Σ_y c_y²` and `Σ_{z ∈ N(x)} t_z²`, gives `A s² − B s + C ≤ 0` for `s = Σ_{u ∈ N(x)} t_u`,
hence `s ≤ capP t`. So `ψ(t_v) ≤ 4t_v² − 2s_v` at every vertex while `Σ_v (4t_v² − 2s_v) = 0`.
*Certificate.* `ψ` is not provably convex, so the record verifies the chord `ℓ` itself; if
`ℓ ≤ ψ` on `[0, (n−1)/2]` and `(n − r)ψ(q) + rψ(q+1) > 0` then
`0 = Σ_v (4t_v² − 2s_v) ≥ Σ_v ℓ(t_v) = (n−r)ψ(q) + rψ(q+1) > 0`, so `T` is impossible.

**Why.** It is the first bound below the constant `1/18`: nothing changes below `n = 33`, then
the gain grows quadratically (`66 → 64` at `33`, `144 → 140` at `50`, `257 → 245` at `67`,
`566 → 529` at `100`, `5029 → 4526` at `300`), about `n²/230` in this range. The bound stays
attained at `n = 9, 15, 27`. The record is a downward search from V007's value with a loop
over `t` at each step; `decide +kernel` settles it at `n = 100` in seconds (37 search steps).

**Witness.** `n₀ = 40`: `93 → 92`.

## Table

| n | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 12 | 13 |
|---|---|---|---|---|---|---|---|---|---|---|
| f n (known) | 1 | 1 | 2 | 2 | 3 | 4 | 6 | 6 | 9 | 10 |
| V000 `C(n,3)` | 1 | 4 | 10 | 20 | 35 | 56 | 84 | 120 | 220 | 286 |
| V001 `C(n,2)/3` | 1 | 2 | 3 | 5 | 7 | 9 | 12 | 15 | 22 | 26 |
| V002 `n⌊(n-1)/2⌋/3` | 1 | 1 | 3 | 4 | 7 | 8 | 12 | 13 | 20 | 26 |
| V003 `n(n+1)/12` | 1 | 1 | 2 | 3 | 4 | 6 | 7 | 9 | 13 | 15 |
| V004 `n·2⌊(n+1)/2⌋/12` | 1 | 1 | 2 | 3 | 4 | 5 | 7 | 8 | 12 | 15 |
| **V005 `n(n+3)/18`** | 1 | 1 | 2 | 3 | **3** | **4** | **6** | **7** | **10** | **11** |


Extended table (`trial claude-fable`; `f` at `14, 15, 16, 26, 27` from the literature notes above):

| n | 3 | 6 | 9 | 10 | 12 | 13 | 14 | 15 | 16 | 18 | 19 | 25 | 26 | 27 | 37 | 50 | 67 | 100 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| f n (known) | 1 | 2 | 6 | 6 | 9 | 10 | 12 | 15 | 15 | ? | ? | ? | 40 | 45 | ? | ? | ? | ? |
| V005 `n(n+3)/18` | 1 | 3 | 6 | 7 | 10 | 11 | 13 | 15 | 16 | 21 | 23 | 38 | 42 | 45 | 82 | 147 | 260 | 572 |
| V006 `n(n+2+n%2)/18` | 1 | 2 | 6 | 6 | 9 | 11 | 12 | 15 | 16 | 20 | 23 | 38 | 40 | 45 | 82 | 144 | 260 | 566 |
| V007 (search) | 1 | 2 | 6 | 6 | 9 | 10 | 12 | 15 | 16 | 19 | 22 | 37 | 40 | 45 | 80 | 144 | 257 | 566 |
| **V008** (search + certificate) | 1 | 2 | 6 | 6 | 9 | 10 | 12 | 15 | 16 | 19 | 22 | 37 | 40 | 45 | **79** | **140** | **245** | **529** |

## What the next improvement would take

The counting bound `deg u + deg v ≤ n + 1` along an edge (`n` for even `n`, by parity), fed
into a maximum-degree count, is what gives `n²/12`. From here:

* **Push the parity/integrality further.** `deg v = 2·t_v` is now available, so the whole count
  can be run on the triangle counts `t_v`: `t_u + t_v ≤ ⌊(n+1)/2⌋` along an edge and
  `3·T = Σ_v t_v`, maximised over an integer `t_v`. For `n ≡ 2 (mod 4)` the integer maximum is
  attained off the real optimum and saves a further constant (`T ≤ (n²-4)/12`); the gain is
  `O(1)` at a positive fraction of `n`, so it is a much smaller step than V003 or V004.
* **A vertex of large degree is very restrictive.** If `deg v = n-1` the graph is a windmill and
  `T = (n-1)/2`; if `deg v = n-2` it is a windmill plus an isolated vertex. Iterating this
  (`deg v = n-3`, …) shows the extremal graph has `Δ ≈ n/2` with *every* edge's two
  neighbourhoods covering all of `V`, a strong condition that the current count does not use.
  Exploiting it should lower the constant `1/12`, but needs a genuinely structural argument.
* **Spencer's `-1`** at `n ≡ 5 (mod 6)`: a single residue class, and a combinatorial argument
  about partial triple systems — now superseded in size by the `n²/12` bounds anyway.
* **Below `c·n²` at all** there is nothing elementary: the truth is `n^{2-o(1)}` by Behrend, and
  the only route down is Fox's removal lemma, whose saving is inverse-tower-type and out of
  formalisation reach.


### Added by `trial claude-fable` (after V006–V008)

* **What the three new ingredients were.** V006: parity at even `n`. V007: the bound
  `Σ_{u ∈ N(v)} t_u ≤ T + t_v` (the non-neighbourhood of `v` spans no triangle) combined with
  the triangle bound per vertex, then the balanced integer distribution (convexity). V008: the
  induced-matching count in the common non-neighbourhood of a non-adjacent pair, averaged per
  vertex, with a convexity certificate computed by the record. All three are in the same
  framework: per-vertex upper bounds on `s_v = Σ_{u ∈ N(v)} t_u` as functions of `t_v`, `T`, `n`,
  against the identity `Σ_v s_v = 2Σ_v t_v²`.
* **Cheap follow-ups inside the framework.** (i) The averaging in V008 loses in two places:
  `c_y t_y ≥ c_y²` and the Cauchy–Schwarz on `Σ_{z ∈ N(x)} t_z²`; keeping `Σ_{z ∈ N(x)} t_z²` as
  a second per-vertex variable (its own convexity in `t_z`) or using `c_y ≤ min(t_x, t_y)` may
  gain a little. (ii) The pair inequality with a *subset* `Z` of the common neighbourhood (only
  the `z` with large `t_z`) is what GPT's argument used for the asymptotic constant; per vertex
  this is not separable, so it needs a different global argument. (iii) The lower root of the
  quadratic is ignored by `capP` (when `capAB < ρ₁` the vertex cannot exist at all); using it
  would let the record declare some `t` infeasible, a small gain.
* **Regular case is `T ≤ n(n+9)/21`** (from the pair inequality with `c = t` and the averaging
  `Σ_y c_y = 4t(t−1)`); the irregular balanced distributions cost about `n²/230` in V008's range.
  A closed form of the type `n²/21 + O(n)` valid for *all* graphs would need a symbolic analysis
  of the worst distribution; the search-based record does it numerically instead.
* **`n ≡ 3 (mod 6)`, `n ≥ 33`:** equality `T = n(n+3)/18` is impossible (no `GQ(2,t)` for
  `t ≥ 5`, by the pair inequality itself: `(t−1)(t−5) ≤ 0`), and V008 already gains there from
  `n = 33` on.
* **Cost.** V008's record scans `T` downward from V007's value (37 steps at `n = 100`, ~500 at
  `n = 300`), recomputing `ψ` on `[0, (n−1)/2]` at every step. A later version should start the
  scan from a closed-form bound proved once (e.g. a proven `n(n+9)/21 + O(n)`), or prove that
  `ok` is monotone in `T` so that a binary search is sound.
* **Files.** Scratch material of this session (Python scripts `bounds*.py`, `validate.py`
  with brute-force checks of the pair inequality on `K₃□K₃`, `K₃□K₃□K₃`, `GQ(2,2)`, `GQ(2,4)`,
  `L(Petersen)`, windmills and Ruzsa–Szemerédi graphs; Lean scratch files `p7a.lean`,
  `p8arith.lean`, `p8graph.lean`) is under `.lake/scratch/RuzsaSzemeredi-Upper/work/`. No
  unfinished version directory exists: V009 is open and empty.

## Problems hit

Nothing blocking. Two things to know for the next submitter: `EdgeDisjointTriangles` is a
`Set.Pairwise` on `cliqueSet 3`, so a clash is produced by exhibiting the two triangles
`{u,v,a}`, `{u,v,b}` via `is3Clique_triple_iff` and showing their intersection is not
subsingleton; and `Finset.card_mul_le_card_mul` is the right double-counting tool in both
directions (V002 for `2·t_v ≤ deg v`, V004 for `deg v ≤ 2·t_v`). All proofs are pure reasoning:
V003 uses 25k of the 200k heartbeats, V004 28k.

Added by `trial claude-fable`: (1) `set`-abbreviations are not propagated into hypotheses
created afterwards, so `omega` sees `farSet G x y` and `F y` as different atoms — fold them
back with `rw [← hF] at h`. (2) A closing `nlinarith` over the seven-variable polynomial
identity of V008's averaging blew the 200k heartbeats; the exact `linear_combination hP1 + hP2
+ hP3` of the three product inequalities costs nothing (`vertex_quadratic` is still the heaviest
declaration, 95k, total 172k of 200k — a V009 must import rather than copy it). (3) `Nat.sqrt`
is defined by well-founded recursion, so the record uses its own bisection `isqrt` with
structural recursion on a fuel of `d + 2`, which the kernel evaluates in ~40 steps.
(4) Products of variables are atoms for `omega`, but only if syntactically identical: `generalize`
them before calling it.
