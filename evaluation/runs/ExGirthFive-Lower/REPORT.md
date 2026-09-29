# ExGirthFive — lower bound track

`f(n)` = largest number of edges of a simple graph on `n` vertices of girth at least `5`
(no triangle, no 4-cycle), i.e. `ex(n; {C₃, C₄})`, OEIS A006856. `nMin = 1`.

Submitters: `baseline claude-opus-5` (V001–V007), `trial claude-fable` (V008 onwards).

## Best known lower bounds in the literature

- **Exact values.** `f` is known exactly for `n ≤ 53` (`f(53) = 181`); the first terms are
  `0, 1, 2, 3, 5, 6, 8, 10, 12, 15, 16, 18, 21, 23, 26, 28, 31, 34, 38, 41` for `n = 1 … 20`
  (OEIS A006856; Garnick–Kwong–Lazebnik 1993 for `n ≤ 24`, Nieuwejaar 1992, Miller–Codish 2017,
  Backelin 2015 and McKay's searches for the rest — provenance as collected in the problem
  README). Three values come from Moore graphs, which meet the upper bound `(n/2)√(n−1)`:
  the 5-cycle (`f(5) = 5`), the Petersen graph (`f(10) = 15`) and the Hoffman–Singleton graph
  (`f(50) = 175`).
- **General construction.** The point–line incidence graph of a projective plane `PG(2,q)` is
  bipartite of girth 6 with `2(q²+q+1)` vertices and `(q+1)(q²+q+1)` edges, giving
  `f(n) ≥ (1/(2√2))·n^{3/2}(1 + o(1)) ≈ 0.354·n^{3/2}` (Erdős–Rényi–Sós 1966, Brown 1966; see
  also Garnick–Kwong–Lazebnik 1993). The affine plane `AG(2,q)` gives the same constant with a
  much simpler incidence rule: `q²` points, `q²` lines `y = a x + b`, `2q²` vertices and `q³`
  edges, i.e. exactly `(n/2)^{3/2}` at `n = 2q²`.
- **Small `n` beyond the exact range.** Goedgebeur, Jooken, Joret and Van den Eede,
  *Improved lower bounds on the maximum size of graphs with girth 5* (arXiv:2508.05562, 2025),
  improve the best known lower bounds for every `74 ≤ n ≤ 198` except `96, 97` by a
  hill-climbing search seeded with known extremal graphs and `(k,5)`-cages; the classical
  small-`n` lower bounds (Garnick–Kwong–Lazebnik 1993) come from explicit graphs and from
  deleting vertices from incidence graphs of planes and from cages.
- **Upper bound / gap.** `f(n) ≤ (n/2)√(n−1)` (Moore-type count), so the leading constant lies
  between `1/(2√2) ≈ 0.354` and `1/2`. Erdős conjectured `f(n) ~ (n/2)^{3/2}`
  ([Erdős problem #573](https://www.erdosproblems.com/573)), open. Ma–Yang (2025) improved the
  lower bound by an additive `c·n^{5/4}`, the first gain since 1976, without moving the constant.

## Starting record

`V000` (seed, SqueezeBench): `record n = 0`.

## V001 — `baseline claude-opus-5`

**Bound.** `record n = n − 1` (and `0` at `n = 0`).

**Idea.** The star with centre the vertex of index `0` is a tree, so its girth is `⊤`: it is
triangle-free, and two distinct vertices have at most the centre as a common neighbour. Its
`n − 1` edges are the image of `univ.erase 0` under `v ↦ s(0, v)`, injectively.

**Why.** The seed record was `0`, so the first step is any bound valid for every `n ≥ 1`; the star
gives one that improves the record at every `n ≥ 2` and costs the kernel nothing. The proof is
adapted from `ExC4/Lower/V001` by the same submitter (`based-on`), plus the extra triangle-free
obligation that girth 5 needs.

**Witness.** `n₀ = 2` (`0 < 1`).

## V002 — `baseline claude-opus-5`

**Bound.** `record n = max (n − 1) (1331 · ⌊n/242⌋)`, i.e. slope `1331/242 = 5.5` edges per
vertex for `n ≥ 242`.

**Idea.** `⌊n/242⌋` disjoint copies of the point–line incidence graph of the affine plane over
`ZMod 11`. Inside a block of `242 = 2·11²` consecutive indices, index `i < 121` is the point
`(i/11, i%11)` and index `121 ≤ i < 242` is the line `y = a x + b` with `a = i/11 − 11`,
`b = i%11`; a point is adjacent exactly to the lines through it. Reading the two digits of an
index as elements of `ZMod 11` needs no case split, because `(11 : ZMod 11) = 0`, so the same
two projections `co1`, `co2` serve points and lines.

The graph is bipartite between points and lines, which gives `CliqueFree 3` directly from the
side inequalities (`omega`). `NoTwoCommonNeighbours` is the plane's two axioms: two points with
two common lines force the lines equal (`a(x₁−x₂) = y₁−y₂` determines the slope once
`x₁ ≠ x₂`, and `x₁ = x₂` forces the points equal), and two lines with two common points force
the points equal. Both are one cancellation in the field `ZMod 11`. The `11³ = 1331` edges per
block are indexed by `(a, b, x) ↦ s(point (x, a x + b), line (a, b))`, injectively.

The proof is uniform in the prime: only the numerals `11`, `121`, `242`, `1331` appear, so the
same script instantiates at any prime, with all index arithmetic left to `omega`.

**Why.** This is the asymptotically best known construction, and at `n = 2p²` it is *exactly*
`(n/2)^{3/2}`, the conjectured truth. As a record it contributes the linear slope `p/2` for all
`n ≥ 2p²`, an improvement at infinitely many `n` (every `n ≥ 242`), not at a single point. Using
blocks keeps the record a cheap ℕ expression. Structure (block graph, `vv`, the injection into
`edgeFinset`) adapted from `ExC4/Lower/V006` by the same submitter (`based-on`); the graph itself
and all of its proofs are new, since `ExC4` may use triangles and this graph may not.

**Witness.** `n₀ = 242` (`241 < 1331`).

## V003 — `baseline claude-opus-5`

**Bound.** `record n = max (V002 n) (1030301 · ⌊n/20402⌋)`: slope `101/2 = 50.5` edges per vertex
for `n ≥ 20402`, ten times the slope of V002.

**Idea.** Exactly the V002 proof at the prime `101` instead of `11`: `10201` points, `10201` lines,
blocks of `20402 = 2·101²` vertices and `101³ = 1030301` edges each. The script is parameterised by
the literals alone, so the whole file is the V002 file with `11, 121, 242, 1331` replaced by
`101, 10201, 20402, 1030301` (`based-on = ["V002"]`); nothing in the mathematics changes, and the
heartbeat cost is unchanged (70594 of 200000, heaviest `plane_card` at 51414) because all the index
arithmetic is `omega` on literals.

**Why.** The affine-plane family is exact at `n = 2p²`, so raising the prime is the substantive
move available: the bound goes from `5.5·n` to `50.5·n` for all `n ≥ 20402`, i.e. at infinitely
many `n`, and `maxWith` keeps V002 wherever it is still better (`242 ≤ n < 20402`).

**Witness.** `n₀ = 20402` (`111804 < 1030301`).

## V004 — `baseline claude-opus-5`

**Bound.** `record n = max (V003 n) (1027243729 · ⌊n/2036162⌋)`: slope `1009/2 = 504.5` edges per
vertex for `n ≥ 2036162`, ten times the slope of V003.

**Idea.** The same script once more at the prime `1009`: `1018081` points, `1018081` lines, blocks
of `2036162 = 2·1009²` vertices with `1009³ = 1027243729` edges. Only the four literals change
(`based-on = ["V003"]`), and the cost is again 70596 heartbeats — the numbers are ℕ literals, so
neither `omega` nor the kernel notices the size.

**Why.** Same reason as V003: on this track each prime is a genuine tenfold gain in slope at
infinitely many `n`, and `maxWith` protects the smaller ranges. This is where the fixed-prime ladder
stops paying: it is time to make the prime depend on `n` (see below).

**Witness.** `n₀ = 2036162` (`101999799 < 1027243729`).

## V005 — `baseline claude-opus-5`

**Bound.** `record n = max (V004 n) (1002101470343 · ⌊n/200280098⌋)`: slope `10007/2 = 5003.5`
edges per vertex for `n ≥ 200280098`.

**Idea.** The V002/V003/V004 script once more at the prime `10007`: `100140049` points,
`100140049` lines, blocks of `200280098 = 2·10007²` vertices with `10007³ = 1002101470343` edges.
Only the four literals change (`based-on = ["V004"]`); the cost is again ~70600 heartbeats.

**Why.** A cheap, safe tenfold gain in slope at infinitely many `n`, taken first so that a record
was banked before starting the parametric construction of V006.

**Witness.** `n₀ = 200280098` (`100669885442 < 1002101470343`).

## V006 — `baseline claude-opus-5`

**Bound.** `record n = max (V005 n) (maxₚ p³·⌊n/(2p²)⌋)`, the maximum taken over the sixteen
primes `11, 31, 61, 127, 251, 509, 1021, 2039, 4093, 8191, 16381, 32749, 65521, 131071, 262139,
524287` — one just below each power of two from `2^4` to `2^19`.

**Idea.** The construction of V002–V005 proved **once, parametrically in the prime**, instead of
once per prime. The block graph is no longer built on indices of `Fin n` with `/` and `%` by
literals (which is what forced a fixed prime: `omega` cannot divide by a variable). It is built on
the structured vertex type `Fin k × ((ZMod p × ZMod p) ⊕ (ZMod p × ZMod p))` — `k` blocks, each a
copy of the points and the lines of the affine plane over `ZMod p` — and then *transported* into
`Fin n` along an arbitrary embedding `e`, which exists because
`Fintype.card = k·2p² ≤ n` (`Function.Embedding.nonempty_of_card_le`). The record graph is
`(PG k p).map e`; the embedding is noncomputable, which is harmless since only `Def.lean` must be
computable.

All the arithmetic is then field arithmetic in `ZMod p`, with no index juggling at all:

- *No triangle*: the graph is bipartite between points and lines, so among any three vertices two
  lie on the same side and are not adjacent. `cliqueFree_map_iff` moves this across `e`.
- *No two common neighbours*: two points on two common lines force `(a₁−a₂)(x₁−x₂) = 0`, hence the
  lines equal once the points differ; two lines through two common points likewise. Transported
  across `e` by injectivity: each adjacency of the image has a unique preimage pair.
- *Edge count*: `(block, a, b, x) ↦ s(e (block, inl (x, a x + b)), e (block, inr (a, b)))` is an
  injection from `Fin k × (ZMod p)³` into the edge finset, so `p³·k` edges.

`Def.lean` then folds `max` over the table of primes, and `Proof.lean` closes `valid` by list
induction on the table, one `norm_num` primality check per entry.

**Why.** This is the step the previous report called "the real step": the prime is no longer frozen
into the script. Consecutive table primes differ by a factor of about `2`, so between block sizes
the envelope loses at most a factor of `2` in slope, and the record now tracks
`c·n^{3/2}` with `c ≈ (1/2)·1/(2√2) ≈ 0.18` over the whole range `242 ≤ n ≤ 2·524287² ≈ 5.5·10¹¹`,
instead of being a single line. At `n = 2p²` for a table prime it is exactly `(n/2)^{3/2}`, the
conjectured truth. The whole file costs 12755 heartbeats of the 200000 budget (against 70600 for
the single-prime V005), so the table can be extended cheaply.

**Witness.** `n₀ = 2·524287² = 549753716738` (`2749766434621192 < 144114363443707903`).


## V007 — `baseline claude-opus-5`

(Accepted by the previous submitter but not described in this report; reconstructed from
`Records/Lower/V007/`.)

**Bound.** `record n = max (V006 n) (maxₚ p³·⌊n/(2p²)⌋)` over a table of 110 primes, one just
below each multiple of `2^(1/4)` from `11` to `2^31` (`2087937811`), so consecutive entries have
ratio about `1.19` and the envelope of the block bounds stays within a factor `1/1.19³ ≈ 0.59` of
`(n/2)^{3/2}` up to `n = 2·2087937811² ≈ 8.7·10¹⁸`.

**Idea.** Exactly V006's parametric proof with a longer table: `V006.block_le` for each prime,
`norm_num` primality for each entry (55205 of the file's 55934 heartbeats), list induction.

**Witness.** `n₀ = 8718968605206943442 = 2·2087937811²`
(`2285620946142342176178116 < 9102332111866754346145142731`).

## V008 — `trial claude-fable`

**Bound.** `record n = max (V007 n) (maxₚ blk p n)` over a table of 217 primes, with

```
blk p n  = p³·⌊n/(2p²)⌋ + part p (n mod 2p²)
part p r = s·(r − s·p),   s = ⌈r/(2p)⌉      (truncated subtraction)
```

The table is `2, 3, 5, 7`, one prime near the geometric mean of each pair of consecutive V007
entries (ratio of the merged table about `1.09`), and the V007 table itself (reused by name).

**Idea.** The `r = n mod 2p²` leftover vertices, isolated in V006/V007, now carry an *induced
subgraph* of one more affine plane: `s` complete parallel classes (`s·p` lines, slopes in a set
`A`) and `m = r − s·p` points (a set `P`). Every point lies on exactly one line of each class,
so the piece has exactly `s·m` edges, and girth `6` is inherited. With `s = ⌈r/(2p)⌉` this is
about `r²/(4p)` edges. Formally, the graph is the pullback (`SimpleGraph.comap`) of V006's
`PG (k+1) p` along an injection from `Fin k × Side p ⊕ (P ⊕ A × ZMod p)`, then pushed into
`Fin n`; `CliqueFree.comap` and a one-line argument give the girth condition, and the edges are
indexed by `Fin k × (ZMod p)³ ⊕ (P × A)`. The general statement is

```
subplane_le : p.Prime → s ≤ p → m ≤ p² → k·2p² + s·p + m ≤ n → k·p³ + s·m ≤ f n
```

and `transport_le` (any girth-5 graph on a finite type of size `≤ n` with `#I` exhibited edges
gives `#I ≤ f n`) is stated once for reuse. `part_spec` is the arithmetic that `part p r` is
such an `(s, m)`; the case `s·p > r` is the empty sub-plane. Cost: 75897 heartbeats, of which
52962 are the `norm_num` primality checks of the 107 new entries.

**Why.** Between block sizes V007 fell to `0.59·(n/2)^{3/2}` (just below `2p²` it still used the
previous prime's full plane); with the sub-plane and the denser table the envelope stays above
`0.82·(n/2)^{3/2}` over the whole range `8 ≤ n ≤ 8.7·10¹⁸` (model computation). The record beats
V007 at 2869 of the first 3000 `n`, and at all but a vanishing fraction of `n` up to `8.7·10¹⁸`;
the exceptions are `n ≤ 7`, `n ∈ {9, 10, 11, 13}` and short runs just above each `2p²`. The small
primes make the construction reach down to `n = 8` (`C₈`, the Pappus graph at `n = 18`,
`AG(2,5)` with `125` edges at `n = 50`, `343` at `n = 98`).

**Witness.** `n₀ = 1000` (`6859 < 10868`; the conjectured truth is `≈ 11180`): the sub-plane of
`AG(2,23)` with `22` classes (`506` lines) and `494` points.

## V009 — `trial claude-fable`

**Bound.** `record n = max (V008 n) (max (blocks2 n) (tail n))` with

```
tail n     = ⌊n/(4q)⌋ · ⌊n/2⌋,   q = sqrtUp (n/2)   (a kernel-friendly ⌊√(n/2)⌋)
blocks2 n  = maxₚ  p³·⌊n/(2p²)⌋ + part2 p (n mod 2p²)        over the V008 table
part2 p r  = max (cand p r s₀) (cand p r (s₀+1)),  s₀ = ⌊r/(2p)⌋,  cand p r s = s·min(r − s·p, p²)
```

**Idea.** (1) *The tail*: the first bound of order `n^{3/2}` valid for **every** `n`. Bertrand's
postulate (`Nat.exists_prime_lt_and_le_two_mul`) gives a prime `p ∈ (q, 2q]` for
`q = ⌊√(n/2)⌋`. The record cannot compute `p`, but the sub-plane of `AG(2,p)` with `⌊n/(4q)⌋`
slope classes and `⌊n/2⌋` points fits into `n` vertices for *every* such `p`
(`⌊n/(4q)⌋ < q+1 ≤ p`, `⌊n/2⌋ < (q+1)² ≤ p²`, `s·p + m ≤ n/2 + n/2`), so `subplane_le` applies
with the prime known only existentially. Value `≈ n²/(8q) ≈ (n/2)^{3/2}/2`: half the conjectured
truth, for all `n`, against the linear tails of every earlier record. The square root is a
binary search by structural recursion on a fuel, because `Nat.sqrt` (well-founded recursion)
gets stuck in `decide +kernel` at 20-digit arguments; only the upper bracket `x < (q+1)²` is
proved, which is all validity needs. (2) *`part2`*: V008's `s = ⌈r/(2p)⌉` is the wrong neighbour
of the balanced `r/(2p)` just above multiples of `2p` (loss up to `r/2` edges); the better of
`⌊r/(2p)⌋` and `⌊r/(2p)⌋+1` is taken, points clipped to `p²` so that every candidate is an actual
sub-plane. Cost: 31401 heartbeats.

**Why.** The tail beats V008 at every `n ≥ 30053270227319479200 ≈ 3·10¹⁹` — infinitely many `n`,
and the record is now `Θ(n^{3/2})` everywhere (within a factor `2` of the truth beyond the table,
within `0.82` inside it). `part2` improves 1198 of the first 3000 `n` and 46716 of the first
`10⁵`, by a few percent (`n = 13`: `12 → 14`, `n = 31`: `44 → 48`, `n = 42`: `85 → 88`).

**Witness.** `n₀ = 10²⁰` (`102129916315531214065351311353 < 176776695300000000000000000000`).

## V010 — `trial claude-fable`

**Bound.** `record n = max (V009 n) (blocks3 n)` with, over the V008 table,

```
blocks3 n   = maxₚ  E p · ⌊n / N p⌋ + part3 p (n mod N p),   N p = 2(p²+p+1),  E p = (p+1)(p²+p+1)
part3 p r   = max (candB p r s₀) (candB p r (s₀+1)),          s₀ = ⌊(r + p) / (2(p+1))⌋
candB p r s = s · (min (r − 1 − s(p+1)) p² + p + 1)   if s(p+1) + 1 ≤ r,  else 0
```

**Idea.** The projective plane `PG(2,p)` instead of the affine plane without vertical lines:
`(p+1)(p²+p+1) = p³ + 2p² + 2p + 1` edges on `2p² + 2p + 2` vertices, i.e. the `2p + 2` extra
vertices (vertical lines, slope points, `∞`, the line at infinity) bring `p` or `p + 1` edges
each, twice the `p/2` per vertex of a fresh block; at `n = N p` this exceeds `(n/2)^{3/2}`. The
plane is coordinatised as affine points `(x, y)` plus one point at infinity per pencil
(`Option (ZMod p)`: slope `a`, or `none` for the vertical pencil), lines `(i, b)` of pencil `i`
with coordinate `b` (`y = a x + b` or `x = b`) plus the line at infinity; `inc` has four clauses.
The single lemma `inc_pts` (no two distinct points on two distinct lines — the hypotheses are
symmetric, so it is also "no two lines through two points") is a case split with one field
cancellation (`coord_inj`). The leftover carries a *partial plane*: `s` pencils (their `s·p`
lines and `s` points at infinity), `m` affine points and the line at infinity, exactly
`s·(m + p + 1)` edges on `m + s(p+1) + 1` vertices; at `s = p + 1`, `m = p² − t` it is the plane
minus `t` affine points, so the range `2p² ≤ r < N p`, where the affine leftover had nothing, is
covered. `pg_le` (V008's `transport_le` on the pullback of the block graph, with finsets `P`, `A`,
`Lf` of the required sizes) is the general statement; `candB_le`/`blk3_le` as in V009. Cost:
50159 heartbeats (`pg_le` 36057).

**Why.** Improves V009 at 2970 of the first 3000 `n` and at 99731 of the first `10⁵`: `n = 14`:
`16 → 21` (Heawood), `n = 26`: `33 → 52`, `n = 62`: `136 → 186`, `n = 114`: `352 → 456`,
`n = 266`: `1360 → 1596`, `n = 2000`: `29838 → 31776`, `n = 10⁵`: `+0.9%`. The worst ratio to
`(n/2)^{3/2}` over the table range rises from `0.70` to `0.815` (at `n = 144`, in the prime gap
`7 → 11`). For `n ≥ 10⁶` the gain is below `0.3%`.

**Witness.** `n₀ = 266 = N 11` (`1360 < 1596`).

## V011 — `trial claude-fable`

**Bound.** `record n = max (V010 n) (hs n)`, `hs n = 175` for `n ≥ 50`, `hs n = tab[n]` for
`n < 50`, with

```
tab = [0, 0, 1, 2, 3, 5, 6, 8, 10, 12, 15, 16, 18, 20, 22, 25, 27, 29, 32, 36, 40, 42, 45, 48, 51,
       55, 58, 62, 66, 70, 75, 78, 82, 86, 90, 95, 99, 104, 109, 114, 120, 124, 129, 134, 139, 145,
       150, 156, 162, 168, 175]
```

**Idea.** The Hoffman–Singleton graph, the `(7,5)`-Moore graph (`50` vertices, `175` edges,
`f(50) = 175`), in Robertson's description: pentagons `P_h` and pentagrams `Q_i` on `ZMod 5`,
vertex `j` of `P_h` adjacent to vertex `h·i + j` of `Q_i`. Its girth is checked once by the kernel
(`hs_check`: for `x ≠ y` at most one common neighbour, none if adjacent; 69910 heartbeats). Since
induced subgraphs keep girth `≥ 5`, one fixed ordering of the vertices (`rank`: pentagon `0`,
pentagram `0`, pentagon `1`, …, each block in an affine order found by a small random search)
yields 50 graphs at once: the prefix of length `n` has `tab[n]` edges, counted by the kernel over
the 175 edges (`count_edges`, one `decide` for all `n`). The first 10 vertices are the Petersen
graph, the first 40 the `(6,5)`-cage, the first 45 the graph minus a pentagon, and `tab[n] = f(n)`
for `n ≤ 12` and `34 ≤ n ≤ 50`. The prefix graph is `HS.comap Subtype.val`, transported into `Fin n`
by V008's `transport_le`; injectivity of the 175-edge indexing is the image-cardinality check
`#(univ.image edgeOf) = 175` (`Finset.card_image_iff`), cheaper than all pairs. Cost: 122878
heartbeats.

**Why.** The plane constructions are weakest at small `n` (`0.6`–`0.8` of the truth for
`n ≤ 60`); the sporadic Moore graph is exact there. The record improves V010 at every `n` from `5`
to `60`: `n = 10`: `12 → 15`, `20`: `33 → 40`, `30`: `52 → 75`, `40`: `84 → 120`, `45`:
`104 → 145`, `50`: `125 → 175`, `60`: `174 → 175`; `PG(2,5)` takes over at `n = 62`.

**Witness.** `n₀ = 50` (`125 < 175`).

## Values

| n | 10 | 50 | 100 | 242 | 1000 | 20402 | 10⁶ | 2036162 | 5.5·10¹¹ | 10¹⁸ | 10²⁰ |
|---|---|---|---|---|---|---|---|---|---|---|---|
| V000 (seed) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| V001 | 9 | 49 | 99 | 241 | 999 | 20 401 | 999 999 | 2 036 161 | 5.5·10¹¹ | 10¹⁸ | 10²⁰ |
| V004 | 9 | 49 | 99 | 1331 | 5324 | 1 030 301 | 50 484 749 | 1 027 243 729 | 2.75·10¹⁵ | 5.0·10²¹ | 5.0·10²³ |
| V006 | 9 | 49 | 99 | 1331 | 5324 | 1 030 301 | 131 872 229 | 1 027 243 729 | 1.44·10¹⁷ | 2.6·10²³ | 2.6·10²⁵ |
| V007 | 9 | 49 | 99 | 1331 | 6859 | 1 030 301 | 344 472 101 | 1 027 243 729 | 1.44·10¹⁷ | 2.39·10²⁶ | 1.02·10²⁹ |
| V008 | 9 | 125 | 343 | 1331 | 10 868 | 1 030 301 | 344 577 206 | 1 027 243 729 | 1.44·10¹⁷ | 3.39·10²⁶ | 1.02·10²⁹ |
| V009 | 9 | 125 | 343 | 1331 | 10 868 | 1 030 301 | 344 577 206 | 1 027 243 729 | 1.44·10¹⁷ | 3.39·10²⁶ | 1.77·10²⁹ |
| V010 | 12 | 125 | 357 | 1331 | 10 899 | 1 030 301 | 345 553 158 | 1 027 243 729 | 1.44·10¹⁷ | 3.39·10²⁶ | 1.77·10²⁹ |
| V011 | 15 | 175 | 357 | 1331 | 10 899 | 1 030 301 | 345 553 158 | 1 027 243 729 | 1.44·10¹⁷ | 3.39·10²⁶ | 1.77·10²⁹ |
| `(n/2)^{3/2}` | 11.2 | 125 | 354 | 1331 | 11 180 | 1 030 301 | 3.54·10⁸ | 1.03·10⁹ | 1.44·10¹⁷ | 3.54·10²⁶ | 3.54·10²⁸ |
| true `f(n)` | 15 | 175 | ≥ 411 (lit.) | only bounds known | — | — | — | — | — | — | — |

Exact values for `33 ≤ n ≤ 53` (OEIS A006856): `87, 90, 95, 99, 104, 109, 114, 120, 124, 129, 134, 139, 145, 150, 156, 162, 168, 175, 176, 178, 181`.

V006 is the first record of the track that grows like `n^{3/2}` rather than linearly over its
range: at `n = 10⁶` it uses the prime `509` (`509³·⌊10⁶/518162⌋ = 131872229`, against `50484749`
for V005), and at `n = 5.5·10¹¹` the prime `524287` (`1.44·10¹⁷` against `2.75·10¹⁵`). Below
`n = 2·31² = 1922` the table still falls back on the prime `11` of V002, so small `n` are
unchanged.

The literature value at `n = 242` is not known exactly, but `0.354·242^{1.5} ≈ 1332`, so a block
construction is within a few edges of the best known bound *at its own block size* (`V003 20402 =
1030301` against `0.354·20402^{1.5} ≈ 1.03·10⁶`) and loses only strictly between block sizes.

## What the next improvement would take

State at the end of the `trial claude-fable` session (2026-09-25): V011 is the record, V012 is open.
The record is now `Θ(n^{3/2})` for every `n` (V009's Bertrand tail, constant `1/2` of the
conjectured truth beyond the prime table), within `0.815`–`1.0` of `(n/2)^{3/2}` over
`61 ≤ n ≤ 8.7·10¹⁸` (V008/V010), and equal to `f(n)` for `n ≤ 12` and `34 ≤ n ≤ 50` (V011).

- **Parked: V012, projective planes over prime-power fields.** The prime gaps `7 → 11`,
  `13 → 17`, `23 → 29`, `31 → 37` are where the record is weakest above `n = 60` (ratio `0.815`
  at `n = 144`). `PG(2,q)` for `q = 8, 9, 16, 25, 27, 32, 49, 64, 81, 121, 125, 128, …` fills them:
  the model gives `+28%` at `n = 146` (`PG(2,8)`, `657` edges), `+10%` around `n = 546`
  (`PG(2,16)`), a few percent up to `n ≈ 10⁵`. Plan: re-prove V010's `pg_le` for an arbitrary
  finite field `F` (`Field F`, `Fintype F`; use a `Prop`-valued incidence to avoid decidability;
  V010's proof uses only field axioms), instantiate with Mathlib's `GaloisField p k`
  (`Mathlib/FieldTheory/Finite/GaloisField.lean`: `GaloisField.card : Nat.card (GaloisField p n)
  = p ^ n` for `n ≠ 0`; the `Fintype` instance is obtained by `Fintype.ofFinite`, so state the
  general lemma with `Fintype.card F = q` and convert), and add `blk3 q n` over a list of
  `(p, k)` pairs to the record with `maxWith`. The directory
  `SqueezeBench/Problems/ExGirthFive/Records/Lower/V012/` holds only the untouched `squeeze new`
  template (`sorry`s); nothing of the plan is written. Rebase it if another submitter lands first.
- **Denser prime table.** Halving the ratio between consecutive primes again (`1.09 → 1.045`,
  about 110 more entries) raises the envelope's worst case between block sizes from about `0.93`
  to `0.965` for `n ≥ 2000`; cost about 55000 heartbeats of `norm_num` primality per 110 primes,
  so it fits in one version together with little else.
- **Extend the table beyond `2^31` with Lucas certificates.** `norm_num` primality is
  `O(√p)`, so the table stops near `2·10⁹`; beyond `n ≈ 3·10¹⁹` the record is the tail, constant
  `1/2`. `Mathlib.NumberTheory.LucasPrimality` (`lucas_primality`: `a^(p−1) = 1` and
  `a^((p−1)/q) ≠ 1` for every prime `q ∣ p − 1`) needs modular exponentiation the kernel can run
  (write square-and-multiply by structural recursion on a fuel and prove it equals `a ^ e % p`)
  and primes with `p − 1` of known factorisation (`p = 2^a·3^b + 1`, so `q ∈ {2, 3}`). About
  `3` exponentiations per prime; 30–40 primes per version. Each octave of primes doubles the
  range of `n` with the near-optimal constant (`0.82` instead of `0.5`).
- **A tail with a better constant** needs either a stronger prime-gap theorem than Bertrand's
  (Mathlib has only `Nat.exists_prime_lt_and_le_two_mul`) or a record that finds the prime
  itself by trial division near `√(n/2)`. The latter gives the optimal constant for all `n` but
  costs `O(n^{1/4} log n)` kernel steps at *every* later evaluation of the record (about `10⁶`
  divisions at `n = 10²⁴`); judged too heavy a burden on later submitters and not done.
- **More sporadic graphs.** V011's pattern (one kernel girth check, prefixes of a fixed order
  counted by one `decide`) costs about `70000 + 30000` heartbeats for a 50-vertex graph; the
  girth check grows like `n³`, so graphs up to about 60–70 vertices fit a version. Candidates:
  the exact extremal graphs for `51 ≤ n ≤ 53` (`176, 178, 181`; V011 gives `175`) and the
  hill-climbing graphs of Goedgebeur–Jooken–Joret–Van den Eede (arXiv:2508.05562) for
  `74 ≤ n ≤ 198` if their adjacency lists are published as data (cite them; the maintainers'
  rule on outside sources applies — see below). Cheaper girth checks (neighbourhood lists
  instead of `50 × 50 × 50` counting) would roughly halve the cost.
- **A two-level leftover** (blocks of a smaller prime on the leftover of a larger one) gains at
  most about `6%` at bad `n` and costs `217²` block evaluations per `record n`; not worth it.
- **Superseded ideas kept for the record:** the fixed-prime ladder of V002–V005, the `2^k`
  table of V006, the single-slope leftover of V008 (fixed in V009).

**Rule on outside sources (maintainers, 2026-09-25).** Code from outside may be used only under
Apache-2.0/MIT/BSD with the notice kept and a one-line source comment; plain mathematical data
(tables, graphs) with a citation; every record's `REPORT.md` lists its sources under *Sources*.
V008–V011 use no outside code; V011 cites Hoffman–Singleton (1960) and OEIS A006856 as data.

## What the next improvement would take (as written after V007 by baseline claude-opus-5)

- **Extend the table.** `Def.lean` may hold 64 KB and the parametric proof costs nothing per
  entry beyond one `norm_num` primality check (515 heartbeats for all sixteen entries together),
  so hundreds of primes fit. Primes just below every power of two up to `2^60`, or a denser table
  (two or three primes per octave), would push the `n^{3/2}` range much further and shrink the
  factor-2 loss between block sizes towards the optimal `1/(2√2)`.
- **A truly asymptotic bound.** To beat every table one must choose the prime *from `n`*: take a
  prime in `[⌊√(n/2)⌋, 2⌊√(n/2)⌋]` by Bertrand's postulate
  (`Nat.exists_prime_lt_and_le_two_mul`). The obstacle is unchanged — `record` must *compute* that
  prime cheaply for the kernel — but with V006's `block_le` the mathematics is already done: it is
  a statement about an arbitrary prime, so only the computable selection is missing.
- **Superseded, kept for the record:** re-instantiate the V002 script at a larger prime `p` — the file is
  literal-parameterised, so only `p`, `p²`, `2p²`, `p³` change, and the heartbeat cost does not move
  (~70600 of 200000). This is what V003 (`p = 101`) and V004 (`p = 1009`) are. `p = 10007` would
  give slope `5003.5` for `n ≥ 200280098`. Diminishing returns: each step only helps beyond its own
  block size, and it never leaves the class of linear bounds.
- **The real step:** make the prime depend on `n` instead of fixing it, turning the family of
  linear bounds into the order-`n^{3/2}` bound `f(n) ≥ (1 + o(1))·(n/2)^{3/2}`. The obstacle is
  that the record function must *compute* the prime cheaply for the kernel while the proof must
  supply `Fact p.Prime` for whatever prime the function picked. The clean route is Bertrand's
  postulate (`Nat.exists_prime_lt_and_le_two_mul` in Mathlib) applied to `⌊√(n/2)⌋`, which
  yields `f(n) ≥ c·n^{3/2}` with `c` a constant factor (about `1/8` of optimal) below
  `1/(2√2)`, but still beats every linear record for large `n`. A table of primes in `Def.lean`
  (at most 64 KB) with a `List.findGreatest`-style lookup is an alternative that keeps the
  optimal constant on a long initial range.
- **Beyond that:** the additive `n^{5/4}` gain of Ma–Yang (2025), or the exact values for
  `n ≤ 53` patched in at single points (cheap but each is one `n` only).

## Problems hit

- `decide`/`decide +kernel` cannot see `f` (it is noncomputable), so every value must come from an
  explicit graph; no small case can be brute-forced.
- Keeping the block size a literal is what makes the proof tractable: all index arithmetic
  (`i % 242`, `i / 11`) is then within reach of `omega`, which fails as soon as the prime is a
  variable (nonlinear `x·p`). (V002–V005; solved in V006 by structured vertex types and `comap`.)
- `omega` treats a nonlinear product as an atom, but `2 * p * s` and `s * p` are *different*
  atoms: state the needed identities (`by ring`) as hypotheses first (V008 `part_spec`).
- `Nat.sqrt` (well-founded recursion) got stuck in `decide +kernel` at a 20-digit argument;
  V009 uses a fuel-based binary search (`sqrtUp`) of which only the upper bracket is proved.
- Inside `first | exact absurd h (by simp) | …`, a failing nested `by` block does not make the
  alternative fail (its error is postponed), so `first` does not backtrack; use `simpa using h`
  or a lemma instead (V010 `PG2_cliqueFree`).
- `#count_heartbeats in theorem …` reports a few heartbeats when `Elab.async` is on, because the
  kernel check runs in a separate task; measure with `set_option Elab.async false` (the budget
  probe does). Measured kernel costs: Hoffman–Singleton girth check 69910, image-cardinality
  injectivity of 175 edges 24532, prefix edge counts for all `n ≤ 50` 8040.
- `SimpleGraph.comap` takes a plain function, not an embedding; `CliqueFree.comap` wants a
  `Copy`, built from `Embedding.comap ⟨φ, hφ⟩ G` (V008).
- Stopping a background script with `pkill -f` on a pattern such as `python3 -` also matches
  other sessions' processes of the same user on this shared machine (it killed one at the end
  of this session). Kill by PID only.

## Scratch files

`.lake/scratch/ExGirthFive-Lower/claude-1051/…/scratchpad/` (this session's directory) holds
the drafts and experiments: `sub1.lean` (V008), `v9.lean` (V009), `v10a.lean`, `v10b.lean`
(V010), `hs_test.lean`, `hs_test2.lean` (kernel costs of the Hoffman–Singleton checks),
`hs_order.json` (the vertex order and prefix counts of V011), `newprimes.json` (the 103
intermediate primes of V008). The value models were run inline (Python) and are described in
the version sections above.
