# ExC4 — lower bound track

`f(n) = ex(n; C₄)`, the largest number of edges in a `C₄`-free simple graph on `n` vertices
(OEIS A006855). `nMin = 1`.

## Literature

- **Asymptotics.** `f(n) = ½ n^{3/2} + O(n^{4/3})`. Upper bound: Kővári–Sós–Turán (1954),
  sharpened by Reiman (1958) to `f(n) ≤ ¼ n (1 + √(4n−3))`. Matching construction: the
  *polarity graph* `ER_q` of Erdős–Rényi–Sós (1966) and Brown (1966).
- **Polarity graph.** For `q` a prime power, `ER_q` has `q² + q + 1` vertices and
  `½ q (q+1)²` edges and is `C₄`-free. Füredi (1996) proved it optimal for every `q > 13`,
  so `f(q² + q + 1) = ½ q (q+1)²` there.
- **Exact values** (A006855; Clapham–Flockhart–Sheehan 1989 for `n ≤ 21`, Yang–Rowlinson 1992
  for `22 ≤ n ≤ 31`, Shao–Xu–Xu for `n = 32`, McKay for `33 ≤ n ≤ 40`):

  | n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 |
  |---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
  | f(n) | 0 | 1 | 3 | 4 | 6 | 7 | 9 | 11 | 13 | 16 | 18 | 21 | 24 | 27 | 30 |

  | n | 16 | 17 | 18 | 19 | 20 | 21 | 31 |
  |---|---|---|---|---|---|---|---|
  | f(n) | 33 | 36 | 39 | 42 | 46 | 50 | 90 |

  From `n = 41` only bounds are known (`132 ≤ f(41) ≤ 133`).
- **Linear term.** Ma–Yang (2023) disproved the conjectured `½ n^{3/2} + n/4 + O(√n)`.

The starting record on this track was `V000 = 0` (the empty graph).

## V001 — `baseline claude-opus-5`

**Bound.** `record n = n − 1`.

**Idea.** The star `K_{1,n−1}`: vertex `0` joined to every other vertex. Two distinct
vertices have at most the centre as a common neighbour, so it is `C₄`-free
(`NoTwoCommonNeighbours` follows from `omega` once the adjacency disjunctions are turned into
arithmetic on `Fin.val`). Its `n − 1` edges are exhibited as the image of
`univ.erase 0` under `v ↦ s(0, v)`, injective, so `n − 1 ≤ #G.edgeFinset ≤ f n`. Counting a
*lower* bound on the edges by an injection avoids any degree-sum argument.

**Why.** The first nontrivial bound on the track, and a reusable skeleton: graph → freeness by
`omega` → edge count by an injection into `edgeFinset`.

**Witness.** `n₀ = 2` (`0 → 1`).

## V002 — `baseline claude-opus-5`

**Bound.** `record n = (n − 1) + ⌊(n − 1)/2⌋ = ⌊3(n − 1)/2⌋`.

**Idea.** The friendship (windmill) graph: hub `0`, and `2k+1 ~ 2k+2` for every `k`, so the
graph is `⌊(n−1)/2⌋` triangles glued at the hub, plus one pendant edge when `n` is even.
Adjacency is `x ≠ y ∧ (x = 0 ∨ y = 0 ∨ (x+1)/2 = (y+1)/2)` on `Fin.val`, which `omega`
handles, including the freeness argument: two vertices share the hub, or the third vertex of
their triangle, but never both. Edges are counted as the disjoint union of the `n − 1` hub
edges with the `⌊(n−1)/2⌋` triangle edges, both exhibited as injective images.

This is the best possible construction in which one vertex is adjacent to all others: if the
hub sees everything, then no two other vertices may have a second common neighbour, so the
rest of the graph is a matching — exactly the friendship graph.

**Why.** It improves the record at every `n ≥ 3` (a factor `3/2` instead of `1`), which is far
preferable to a pointwise patch.

**Witness.** `n₀ = 3` (`2 → 3`).

## V003 — `baseline claude-opus-5`

**Bound.** `record n = max (⌊3(n−1)/2⌋) (50·⌊n/21⌋)`.

**Idea — the block construction.** Fix a `C₄`-free graph `H` on `k` vertices with `m` edges and
put `⌊n/k⌋` disjoint copies of it inside `Fin n`: adjacency is
`x / k = y / k ∧ H.Adj (x % k) (y % k)`. A neighbour never leaves its block, so if `x, y` have
two common neighbours `u, v` then all four lie in one block and their residues contradict the
`C₄`-freeness of `H`; hence `f(n) ≥ m·⌊n/k⌋`, a linear bound of slope `m/k`.

Here `H` is the Erdős–Rényi polarity graph of `PG(2,4)`: the 21 points of the projective plane
over `GF(4)`, with `x ~ y` iff `x·y = 0` — `k = 21`, `m = ½·4·5² = 50`, slope `50/21 ≈ 2.381`.
`H` is stored as a table of 21 neighbourhood bitmasks, so adjacency is one `Nat.testBit`;
`C₄`-freeness is checked as `∀ x y, x ≠ y → #{u | x ~ u ∧ y ~ u} ≤ 1` (`441 × 21` cheap
evaluations, 17k heartbeats), and the 50 edges are listed so the edge count is again an
injection into `edgeFinset`, this time from `range ⌊n/21⌋ ×ˢ range 50`.

**Why.** It improves the record at all but finitely many `n` (slope `2.381` against `1.5`), and
it is the first record on the track whose graph is genuinely extremal rather than ad hoc.
Folded in with `maxWith`, so the small-`n` behaviour of V002 is kept.

**Witness.** `n₀ = 21` (`30 → 50`, the exact value of `f(21)`).

## V004 — `baseline claude-opus-5`

**Bound.** `record n = max (V003 n) (90·⌊n/31⌋)`.

**Idea.** The same block construction with a larger plane: the polarity graph of `PG(2,5)`, on
the `31` points over `GF(5)`, with `m = ½·5·6² = 90` edges. Slope `90/31 ≈ 2.903` against the
`50/21 ≈ 2.381` of V003. The proof is V003's, re-instantiated at `k = 31`, `m = 90`; the only
change of substance is that the data checks must run as `decide +kernel`, since at `Fin 90` the
elaborator's `decide` exceeds `maxRecDepth` and the budget rules forbid raising it.

**Why.** The slope of the block construction is `m/k ≍ ½√k`, so each larger prime power is a
real gain; `q = 5` was the largest step that stayed comfortably inside the heartbeat budget in
the time available.

**Witness.** `n₀ = 31` (`50 → 90`, the exact value of `f(31)`).

## V005 — `baseline claude-opus-5`

**Bound.** `record n = max (V004 n) (224·⌊n/57⌋)`.

**Idea.** The block construction of V003/V004 with the polarity graph of `PG(2,7)`: `57`
vertices, `224 = ½·7·8²` edges, slope `224/57 ≈ 3.93`. The `C₄`-freeness check is the
`Θ(k²)` bitmask test the V004 report asked for: for distinct vertices `a ≠ b` the kernel checks
`mask a &&& mask b = 0 ∨ mask a &&& mask b = 2 ^ log2 (…)`, i.e. at most one common neighbour,
and a small lemma (`eq_of_testBit_two_pow`) turns that into the freeness proof. The `224` edges
are still listed explicitly and their injectivity checked by `decide +kernel`
(`Fin 224 × Fin 224`, the heaviest declaration of the file at `77k` heartbeats).

**Witness.** `n₀ = 57` (`100 → 224`; the report of this version was not written by its
submitter and is reconstructed here from its files and the README row).

## V006 — `trial claude-fable`

**Bound.** `record n = max (V005 n) (v n)` with `v n = max (blockBest n) (delBest n)`, where,
writing `N_q = q² + q + 1` and `E_q = q (q+1)² / 2` for the order and size of the polarity graph
`ER_q`, and `PP` for the prime powers,

```
delChain j t m  = m                               if j = 0
                = delChain (j−1) (t−1) (m − ⌊2m/t⌋)  otherwise      (greedy vertex deletion)
delBest n   = max { delChain (N_q − n) N_q E_q : q ∈ PP, n ≤ N_q, q² ≤ 2n }
small r     = max (V005 r) (delBest r)
blockBest n = max { ⌊n/N_q⌋·E_q + small (n mod N_q) : q ∈ PP, N_q ≤ n }
```

**Idea.** Four general theorems, all in `Records/Lower/V006/Proof.lean` and reusable by later
versions:

1. *The polarity graph of every prime power order, without projective geometry*
   (`er_bound`, `er_primePow`). For a finite field `F` of order `q`, take the vertex set
   `(F × F) ⊕ Option F` and the adjacency `(a,b) ~ (c,d) ⇔ (a,b) ≠ (c,d) ∧ ac = b + d`,
   `(a,b) ~ some a`, `some m ~ none`. This is `ER_q` for the bilinear form `xx' − yz' − zy'`
   in the affine chart `z = 1`, with `some m = (1:m:0)` and `none = (0:1:0)`. `C₄`-freeness is
   an 81-case analysis in which the only real case is two affine points: their common
   neighbours `(e,g)` satisfy `(a − c) e = b − d`, so `a ≠ c` leaves one solution and `a = c`
   forces `b = d`. The edge count is a degree sum: `(a,b)` has degree `q + 1 − [a² = 2b]`,
   `some m` has `q + 1`, `none` has `q`, and there are at most `q` affine absolute points
   (`a² = 2b` determines `b` in odd characteristic and forces `a = 0` in characteristic two),
   so `2|E| ≥ q (q+1)²`. `GaloisField p k` supplies the field for every prime power, so no
   table is needed for any `q`.
2. *Superadditivity* `f a + f b ≤ f (a + b)` (`f_superadd`): the disjoint sum `G ⊕g H` of
   extremal graphs, transported to `Fin (a+b)` by `finSumFinEquiv`. The extremal graphs come
   from Mathlib's `lt_extremalNumber_iff` (`exists_graph`).
3. *Vertex deletion* `f (n+1) − ⌊2 f(n+1)/(n+1)⌋ ≤ f n` (`f_del`): a vertex of minimum degree
   has degree at most the average, and the graph induced on the other vertices (`comap` along
   `Fin.succAboveEmb`) loses at most that many edges. `g_mono` shows `m ↦ m − ⌊2m/k⌋` is
   monotone, so the bound may be iterated from any lower bound, not only from `f` itself.
4. *Kernel-checkable prime powers* (`isPrimePowB`, trial division by `List.range'`), with the
   proof `isPrimePowB q = true → ∃ p k, p.Prime ∧ k ≠ 0 ∧ q = p ^ k`.

The record is then two loops over prime powers with the invariants `delLoop n fuel q ≤ f n`
and `blockLoop n fuel q ≤ f n`. Evaluation is cheap: the witness comparison costs `352`
heartbeats, and even `n = 1000` costs about `3000`.

**Why.** It is the "real target" of the V004 report: the bound is `Θ(n^{3/2})` with the right
constant, `record n / n^{3/2}` staying between `0.46` and `0.52` for `n ≤ 10⁴`, and it improves
V005 at `985` of the first `1000` values of `n` (all `n ≥ 10` except `21, 22, 31, 32, 57` and a
few more), matching the known value of `f` at `n = 11, 12, 13, 21, 31` and the best known
construction at `n = 73, 91, 133, 183, 273, …`.

**Witness.** `n₀ = 133` (`448 → 792`, the polarity graph `ER_11`; Reiman's bound gives
`f(133) ≤ 798`).

## V007 — `trial claude-fable`

**Bound.** `record n = max (V006 n) (v n)` with `v = pin 1 (max anchorBest blockBest)`:

```
tbl n        = the edge count of an explicit C₄-free graph on n vertices, 8 ≤ n ≤ 49
               (11, 13, 16, 18, 21, 24, 27, 30, 33, 36, 39, 42, 46, 50, 52, 56, 59, 63, 67, 71,
                76, 80, 85, 90, 92, 96, 102, 106, 110, 113, 117, 122, 127, 132, 137, 142, 148,
                154, 157, 163, 168, 174), else 0
anchorBest n = max (tbl n) (max { delChain (a − n) a (tbl a) : n < a ≤ 49 })
small r      = max (V006 r) (anchorBest r)
blockBest n  = max { k·E_q + (k − 1) + small r + [r ≥ 1] : q ∈ PP, N_q ≤ n, k = ⌊n/N_q⌋, r = n mod N_q }
```

**Idea.** Two things. (1) *Tables.* The extremal graphs for `n ≤ 40` and the best known graphs
for `41 ≤ n ≤ 49` are taken from the Afzaly–McKay database
(`users.cecs.anu.edu.au/~bdm/data/extremal.html`, files `c4_nNeE.s6`), decoded from sparse6
and stored as lists of neighbourhood bitmasks. A generic theorem `table_bound` turns any such
list `L` into `tableEdges L ≤ f L.length`, provided the kernel confirms `tableOK L`: symmetry
and irreflexivity by a running-index scan (`symFrom`), `C₄`-freeness by the pairwise test
`atMostOneBit (L[i] &&& L[j])` over all `i < j` (`pairsOK`, no list indexing), and the edge
count as half the sum of popcounts. The graph is the symmetrised relation
`i ~ j ⇔ i ≠ j ∧ bit j of L[i] ∧ bit i of L[j]`, so it is a `SimpleGraph` for every list and the
checks are only needed for the count. All `42` tables cost `69k` heartbeats together, about
`1.2·k²` per graph of order `k`. V006's `delChain`/`f_del` then extend every table downwards,
which is why the tables are worth having even where a smaller table exists. (2) *Bridges.* One
edge between two `C₄`-free graphs lies on no cycle, so `f a + f b + 1 ≤ f (a + b)` for
`a, b ≥ 1` (`f_bridge`, from `SimpleGraph.sum`, `edge` and `card_edgeFinset_sup_edge`); the
block decompositions gain `⌊n/N_q⌋` edges, which is small but at infinitely many `n`.

A local search (iterated greedy, 40 s per `n`) for `50 ≤ n ≤ 62` stayed below V006 everywhere
(e.g. `200` against `224` at `n = 57`), so no anchors beyond `49` were added.

**Why.** It closes the small-`n` gap completely: the record now equals `f(n)` for every
`n ≤ 40` and the best known bound for `41 ≤ n ≤ 49` (`24 + 9` values improved, by up to `14`
edges at `n = 36`), and the bridges improve `874` of the first `3000` values of `n` in all.

**Witness.** `n₀ = 40` (`115 → 127 = f(40)`).

## V008 — `trial claude-fable`

**Bound.** `record n = max (V007 n) (v n)` with `v = pin 1 (max colBest blockBest)`:

```
colN q c   = c q + c + 1,   colVal q c = (c² q + 2 c q + c + 1) / 2        (1 ≤ c ≤ q − 1)
colDel q n = delChain (colN q c − n) (colN q c) (colVal q c)  for c = ⌈(n−1)/(q+1)⌉, if c + 1 ≤ q
colBest n  = max { colDel q n : q ∈ PP, q² ≤ 2n }
blockBest  = V007's block decomposition with bridges, the leftover bounded by max (V007 r) (colBest r)
```

**Idea.** The *sub-polarity graph* on `c` columns: inside the explicit model of `ER_q`
(V006), keep the affine points `(m, d)` of `c` columns `m ∈ M` (with `0 ∉ M`), their `c` points at
infinity `some m` and the point `none`. It is the induced subgraph of `ER_q` on
`c q + c + 1` vertices (formally `(ER F).comap` along an injection
`(Fin c × F) ⊕ Option (Fin c) ↪ ERV F`, so `C₄`-freeness is inherited), and its degree sum is
computed exactly as in V006: `(m, d)` has `c + 1 − [m² = 2d]` neighbours (one in each of the
`c` columns, plus `some m`), `some m` has `q + 1`, `none` has `c`, and each column has at most
one absolute point because `m ≠ 0`. Hence `2|E| ≥ c² q + 2 c q + c`. The point of the family is
that deleting whole columns is much cheaper than deleting vertices one at a time: the `q − c`
deleted columns are dense (pairwise `q` edges, plus their `some m` hubs), so at
`n = c q + c + 1` the bound beats the greedy chain from `ER_q` by about `C(q−c, 2)·q/…`, e.g.
`549` against `540` at `n = 109` (`q = 11, c = 9`), `935` against `924` at `n = 155`
(`q = 13, c = 11`). Between two such anchors the greedy chain `delChain` of V006 continues from
the anchor above. The prime-power instantiation needs `c` distinct nonzero field elements,
obtained from `Function.Embedding.nonempty_of_card_le` into `univ.erase 0` of `GaloisField p k`.

A simulation of the *true* minimum-degree greedy on the actual `ER_q` shows about one edge
gained per deleted vertex over the average-degree chain (up to `36` for `q = 11`, `93` for
`q = 16`); the column family recovers roughly half of that in closed form for every prime
power. Partial columns (a closed form for every `n`, not only `n ≡ 1 mod (q+1)`) were checked
in simulation and add nothing beyond the chains between anchors.

**Why.** It improves V007 at `1701` of the first `3000` values of `n` (first at `n = 61`), by
up to `1.7%`, at infinitely many `n`: every window below a prime-power order.

**Witness.** `n₀ = 109` (`540 → 549`; `9` columns of `ER_11`).

## Values

| n | 1 | 3 | 5 | 10 | 21 | 31 | 62 | 100 | 1000 |
|---|---|---|---|---|---|---|---|---|---|
| V000 (start) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| V001 `n−1` | 0 | 2 | 4 | 9 | 20 | 30 | 61 | 99 | 999 |
| V002 `⌊3(n−1)/2⌋` | 0 | 3 | 6 | 13 | 30 | 45 | 91 | 148 | 1498 |
| V003 `max(V002, 50⌊n/21⌋)` | 0 | 3 | 6 | 13 | 50 | 50 | 100 | 200 | 2350 |
| V004 `max(V003, 90⌊n/31⌋)` | 0 | 3 | 6 | 13 | 50 | 90 | 180 | 270 | 2880 |
| V005 `max(V004, 224⌊n/57⌋)` | 0 | 3 | 6 | 13 | 50 | 90 | 224 | 270 | 3808 |
| V006 (prime-power `ER_q`, blocks, deletion) | 0 | 3 | 6 | 15 | 50 | 90 | 238 | 462 | 15881 |
| V007 (tables `n ≤ 49`, bridges) | 0 | 3 | 6 | 16 | 50 | 90 | 238 | 464 | 15882 |
| V008 (sub-polarity graphs on `c` columns) | 0 | 3 | 6 | 16 | 50 | 90 | 241 | 467 | 15882 |
| true `f(n)` | 0 | 3 | 6 | 16 | 50 | 90 | ≤ 258 | ≤ 523 | ≤ 16055 |

The last row gives Reiman's upper bound where the value is unknown. Values at `n = 41 … 49` are
known only as bounds (Afzaly–McKay data: `132, 137, 142, 148, 154, 157, 163, 168, 174` from
below); V006 gives `120, 126, 132, 138, 144, 150, 156, 162, 168` there and V007 the Afzaly–McKay
values.

## What the next improvement would take (after V008)

The record now is: exact for `n ≤ 40`, the best known bound for `41 ≤ n ≤ 49`, and
`Θ(n^{3/2})` with the right constant beyond (`record n / n^{3/2}` between `0.46` and `0.52`).
What is left is lower order: the windows between prime-power orders. In order of expected value:

- **Certified deletion sets from tables of `ER_q` (unfinished; the most promising next step).**
  A simulation of the *true* minimum-degree greedy on the actual `ER_q`
  (`.lake/scratch/ExC4-Lower/claude-1051/erdel.py`, which builds `ER_q` for prime powers with
  `GF(p^k)` arithmetic) gains about one edge per deleted vertex over the average-degree chain
  `delChain`: after `j` deletions the gain is roughly `j − 2`, reaching `12` (`q = 7`), `17`
  (`q = 8`), `22` (`q = 9`), `36` (`q = 11`), `56` (`q = 13`), `93` (`q = 16`). V008's columns
  recover about half of this in closed form; the rest needs the concrete graph. Plan:
  generalise V007's `table_bound` to an *induced-subgraph* bound: for a table `L` of `k` masks
  and a bitmask `T` of kept vertices, `(Σ_{i ∈ T} popcount (L[i] &&& T)) / 2 ≤ f (popcount T)`.
  `C₄`-freeness is inherited from `tableOK L`, the degree of `i` in the induced graph is
  `popcount (L[i] &&& T)` (same proof as `tblGraph_degree`), and the kernel cost per anchor is
  one popcount per row, about `0.2·k²` heartbeats (measured: `cnt70 = 978` for `k = 70`).
  With `1.2·k²` for the table itself this allows `ER_9` (`k = 91`: `10k` + `1.7k` per anchor),
  `ER_11` (`k = 133`: `21k` + `3.5k` per anchor) and `ER_13` (`k = 183`: `40k` + `6.7k` per
  anchor) in one version, with roughly ten anchors each, `delChain` between anchors, and the
  anchors also usable as remainders in `small`. Expected gain: `10 – 30` edges for
  `60 ≤ n ≤ 183` (finitely many `n`, but about `120` of them). The deletion sets should be
  found offline by local search on the loss `Σ_{v∈S} deg v − e(S)` (swap moves starting from
  the greedy order); the script `.lake/scratch/ExC4-Lower/claude-1051/indsearch.py` does this
  for `q = 9, 11, 13`, `j` even up to `40 / 60 / 60`, `20 s` per `j`, and writes
  `indsearch.json`, **but it was never run**: its background launch used a relative path
  after `cd` and failed silently, so there is no data yet. Run it from the project root with
  absolute paths (about 50 minutes), then generate the `ER_q` mask tables from the same
  script's `ER(q)` and the kept-vertex masks `T = all ones minus S`.
- **Structured deletions with exact counts.** For `q = 2^k`, deleting `some 0` (the common
  neighbour of the `q + 1` absolute points in the V006 model, where the absolute affine points
  are `(0, d)`) together with `r − 1` absolute points keeps exactly `E_q − (q−1) r − 2` edges
  (`3 ≤ r ≤ q + 2`; Firke–Kosek–Nash–Williford 2013 give the degrees). For square `q = s²`,
  deleting the subplane `ER_s` gives `f(q² − s) ≥ ½ q (q² − 1) − ½ s (q − 1)`
  (Abreu–Balbuena–Labbate 2010). Both are now partly covered by V008's columns and worth at
  most `O(q)` edges in `O(q)`-wide windows; both need an "edges after deleting a set" lemma
  `e(G − S) = e(G) − Σ_{v∈S} deg v + e(S)` over the explicit `ER` model.
- **Averaging is useless.** The bound `f n ≥ ⌈E_Q · n(n−1)/(N_Q(N_Q−1))⌉` from a random
  `n`-subset of `ER_Q` is exactly the floor-free greedy chain (`m ↦ m(t−2)/t` telescopes to
  `(N−j)(N−j−1)/(N(N−1))`), and the chain with floors `m − ⌊2m/t⌋ ≥ m(t−2)/t` is at least as
  large, so `delChain` already dominates it.
- **Not worth it.** A full memoised dynamic programme over decompositions gains at most `0.14%`
  at `81` of the first `3000` values (`dp.py`); partial columns add nothing beyond the chains
  between column anchors (`plan8.py`); a local search for whole graphs at `50 ≤ n ≤ 62`
  (`sa.py`, `40 s` per `n`) stayed below the deletion chains everywhere.

### Scratch files (all under `.lake/scratch/ExC4-Lower/claude-1051/`, kept between sessions)

| file | content |
|---|---|
| `sim.py`, `rec7.py`, `sim8.py`, `plan7.py`, `plan8.py`, `dp.py` | Python models of the records V005–V008 (values agree with `#eval` of the Lean definitions), the DP comparison, and the column-anchor comparison |
| `erdel.py` | `ER_q` over `GF(q)` for `q ∈ {7, 8, 9, 11, 13, 16, …}`, true greedy deletion versus `delChain` |
| `indsearch.py` | the (unrun) local search for dense deletion sets in `ER_9`, `ER_11`, `ER_13` |
| `mckay/`, `mckay.json`, `s6.py`, `c4_all.tar.gz` | the Afzaly–McKay sparse6 files, their decoder, and the decoded masks used in V007 |
| `sa.py`, `sa_50_75.log` | iterated-greedy graph search and its (negative) results for `50 ≤ n ≤ 62` |
| `ER1.lean`, `Glue.lean`, `Prime.lean`, `Cost.lean`, `Tbl.lean`, `Tables.lean`, `Bridge.lean`, `Sub.lean`, `Bench.lean` | the scratch developments behind V006–V008 and the heartbeat micro-benchmarks (`lake exe squeeze budget-probe <file>` works on scratch files) |

## What the next improvement would take (as written after V004)

- **More blocks of the same kind.** Straight continuation: `q = 7` (`k = 57`, `m = 224`, slope
  `3.93`), `q = 8` (`k = 73`, `m = 324`), `q = 9`, `q = 11`, … Each is a copy-and-paste of V004
  with new tables. The obstacle is the computation budget: the `C₄`-freeness check is
  `Θ(k³)` as written (`∀ x y` over a filter of size `k`), which at `k = 31` already costs 16k
  of the 200k heartbeats, so `k = 57` would not fit. To go further the check has to drop to
  `Θ(k²)`: with the bitmasks already in the record, `x ≠ y → (mask x &&& mask y)` has at most
  one bit set, i.e. `m &&& (m − 1) = 0`, is `k²` GMP operations — but it then needs the bit
  lemma "`m &&& (m−1) = 0`, `testBit m c`, `testBit m d` ⟹ `c = d`", which Mathlib does not
  seem to have ready-made.
- **The real target.** All of the above are linear, while `f(n) ~ ½ n^{3/2}`. Closing that gap
  means formalising `ER_q` for general `q`: the points of `PG(2,q)` over `ZMod p` (or a general
  finite field), adjacency `x·y = 0`, `C₄`-freeness from "two distinct points lie on a unique
  line", and the edge count `½q(q+1)²`. Then `f(n) ≥ ½q(q+1)²·⌊n/(q²+q+1)⌋` with `q` the
  largest prime power below `√n`, and Bertrand's postulate (`Nat.exists_prime_lt_and_le_two_mul`,
  which Mathlib has) turns that into `f(n) ≥ c·n^{3/2}` for an explicit `c`. This is the
  substantial piece of work the track is really asking for.

## Problems hit

- `decide` at `Fin 90` exceeds the elaborator's `maxRecDepth`, and `set_option maxRecDepth` is
  forbidden by the budget rules. `decide +kernel` sidesteps it and is also cheaper.
- `SimpleGraph`'s `symm`/`loopless` fields are `Std.Symm`/`Std.Irrefl` in this toolchain, so
  they need an explicit anonymous constructor, not `intro`.
- Lower-bounding `#G.edgeFinset` by an injection from an explicit index set is much lighter
  than any degree-sum argument, and is what every version here uses.
- (V006–V008) `omega` atomises nonlinear subterms such as `k * (2 * m / k)` or `n / N q * E q`,
  so it can finish goals mixing them with linear facts; when it fails, `generalize` the
  products first so that the counterexample shows what it treated as atoms.
- (V006) `Fintype (G.map f).edgeSet`-style instance mismatches (`fintypeEdgeSet` against
  `fintypeEdgeSetSup`) are best closed by `convert card_edgeFinset_map e K`.
- (V007) `simp` unfolding a closed loop such as `anchorLoop 0 49 1` times out; a closed
  evaluation is `decide +kernel` (`anchorBest 0 = 0`, `small 0 = 0`), a few hundred heartbeats.
- (V008) `rcases` patterns for `Option` are in constructor order, `none | some`, so
  `(m | _)` binds nothing to `m`; write `(_ | i)`.
- (V008) Section variables `[Fintype F] [DecidableEq F]` unused by a lemma give linter
  warnings; split the sections instead of `omit`.
- The background launches of `sa.py` and `indsearch.py` used a path relative to the project
  root after `cd` into the scratch directory, so the shell could not open the log file and the
  scripts never ran; use absolute paths (`$TMPDIR` is absolute) and check the log exists.
