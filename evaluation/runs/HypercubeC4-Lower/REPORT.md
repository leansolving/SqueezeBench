# HypercubeC4 — lower bound track

`f(n) = ex(Qₙ, C₄)`: the largest number of edges in a `C₄`-free subgraph of the `n`-dimensional
hypercube. Erdős Problem #86, open, \$100 prize.

## Literature

- **Conjecture (Erdős, 1991).** `f(n) = (½ + o(1)) · n2ⁿ⁻¹`. Erdős, *On some of my favourite
  problems in graph theory and block designs*, Matematiche 45 (1990) 61–73; see also
  erdosproblems.com/86.
- **Lower bounds.**
  - The parity construction gives `½ · n2ⁿ⁻¹ = n·2ⁿ⁻²`: keep the edge `{x, x+eᵢ}` when the bits of
    `x` other than `i` have even sum. Folklore; it is the leading term of every construction
    below.
  - Guan (credited by Chung, *J. Graph Theory* 16 (1992) 273–286, and by Erdős): `(n+3)·2ⁿ⁻²`
    plus lower-order terms, i.e. `½(n + 3 + o(1))2ⁿ⁻¹`.
  - **Best known:** Brass, Harborth and Nienborg, *J. Graph Theory* 19 (1995) 17–23:
    `f(n) ≥ ½(n + √n)·2ⁿ⁻¹` for `n = 4ʳ`, and `f(n) ≥ ½(n + 0.9√n)·2ⁿ⁻¹` for all `n ≥ 9`.
- **The Brass–Harborth–Nienborg construction** (as described by B. Stanton, *A generalization of
  the methods of Brass, Harborth, and Nienborg*, arXiv:1405.5957, and formalised in Lean 4 in a
  public 2026 Justin Sun Prize submission, JSP-000102, file `Erdos86.lean`, Apache-2.0). Colour
  the edges of `Q₄` with three colours `a/e/o` such that `e` and `o` are disjoint perfect
  matchings and every square contains an `e`-edge and an `o`-edge (there are 16 `a`-edges).
  Given a `C₄`-free subgraph of `Q_m` given by a keep-predicate, blow every coordinate up into a
  block of 4: inside block `w`, keep an `e`-edge iff the parity of the bits outside the block is
  even, an `o`-edge iff it is odd, and an `a`-edge iff the `w`-edge of `Q_m` at the vector of
  block parities is kept. This is `C₄`-free, and if `|E| = (m + s)·2^{m-2}` then the new graph
  has `(4m + 2s)·2^{4m-2}` edges: the excess `s` doubles. From `Q₁` (`s = 1`) this gives
  `Q_{4ʳ}` with `s = 2ʳ = √n`, and adding a coordinate coloured by the parity of the old ones
  keeps `s`, so `f(n) ≥ (n + 2^⌊log₄ n⌋)·2ⁿ⁻²` for all `n ≥ 1` (this is V006).
  Blocks of size 1, 2, 3 (templates: the trivial one; `e = {*0}`, `o = {*1}`; `e = {*00, 0*1, 11*}`,
  `o = {*10, 1*1, 00*}`) can be mixed with blocks of size 4: with base `Q_m`, `m = 4ʳ`, and
  `n − m = 3t + d`, `t` blocks of size 4, one of size `d + 1` and the rest of size 1 give
  `f(n) ≥ (n + σ)·2ⁿ⁻²` with `σ = (m + t + ½·[d = 2])/2ʳ`; at `n = 6, 7` this is `132 = f(6)`
  and `304`, the best known values.
- **Small values and the fully frustrated Ising model.** Minamoto, arXiv:2603.29127 (2026),
  revised August 2026 (repository `minamominamoto/c4free-hypercube`, MIT): `f(8) ≥ 682`, via the
  connection to the *fully frustrated* Ising model on `Qₙ` (Derrida, Pomeau, Toulouse,
  Vannimenus, *J. Physique* 40 (1979) 617; Marinari, Parisi, Ritort, *J. Phys. A* 28 (1995)
  327). With couplings `J(x, x ⊕ 2ⁱ) = (−1)^{popcount(x mod 2ⁱ)}` every square has an odd number
  of negative couplings, so for *any* spin configuration the satisfied bonds meet every square
  in 1 or 3 edges ("odd-square" sets) and form a `C₄`-free subgraph; maximising them is the
  ground-state problem, `f(n) ≥ g(n) := n2ⁿ⁻¹ − U_min(n)`. Known: `g(6) = 132`, `g(7) = 304`,
  `g(8) = 682`; MPR 1995 reached `1532` at `n = 9` (upper bound for `g(9)`: 1536). All fully
  frustrated couplings on `Qₙ` are gauge equivalent (squares span the cycle space).
- **Signed hypercubes.** Laplante, Naserasr, Sunny, Wang, *Sensitivity conjecture and signed
  hypercubes*, ACM ToCT 18 (2026) (HAL hal-04080411, 2023), and Z. Wang, Problem 14B-2,
  *Communications in Combinatorics* (Dec. 2025): the frustration index of the fully frustrated
  `Qₙ` satisfies `(n − √n)2ⁿ⁻² ≤ U_min(n) ≤ 2ⁿ⁻²(n − (n + 2·4ᵏ − m/2)/(3·2ᵏ))` for
  `4ᵏ ≤ n < 4ᵏ⁺¹`, `m ∈ {0,1,2}`, `n + m ≡ 1 (mod 3)`. The constructive side is *exactly*
  V007's bound. The integer-field bound `E₀/N ≥ −(n + ab)/(2(a + b))` (`a, b` consecutive
  integers of the parity of `n` around `√n`) shows the odd-square value `g(n)` equals V007's
  bound at `n = 10, 13, 15, 16, 17, 19`, and leaves room only at `n = 8, 9, 11, 12, 14, 18, …`
  (`g(9) ≤ 1536`, `g(11) ≤ 7296`, `g(12) ≤ 15700`, `g(14) ≤ 72362`, `g(18) ≤ 1454898`).
  Physics folklore (Parisi–Potters 1995) conjectures `E₀/N → −√n/2`, i.e. the excess `√n`, so no
  asymptotic gain over BHN is expected from this route.
- **Upper bounds.** `f(n) ≤ (0.60318 + o(1))·n2ⁿ⁻¹` (Baber, arXiv:1201.3587, flag algebras);
  `0.6068` (Balogh–Hu–Lidický–Liu, *European J. Combin.* 35 (2014) 75–85); `α ≈ 0.623`
  (Chung 1992). Elementary: `f(n) ≤ ¾·n2ⁿ⁻¹` by double counting.
- **Exact values** (OEIS [A245762](https://oeis.org/A245762), offset 1):
  `f(1..6) = 1, 3, 9, 24, 56, 132`; `f(6) = 132` is Harborth–Nienborg, *Bull. ICA* 12 (1994)
  55–60. `f(7) ∈ [304, 308]`.

All constructions below are checked in Lean against `HypercubeC4.le_f_of_not_hasSquare`: exhibit a
subgraph of the cube with no *square* (`Def.lean`'s `HasSquare`), and count its edges.

## Starting record

`V000` (SqueezeBench seed): `record n = 0`.

## V001 — baseline claude-opus-5

**Bound.** `f(n) ≥ n · 2ⁿ⁻²` for all `n ≥ 1` (this is `½ · n2ⁿ⁻¹`, Erdős's conjectured leading
term; at `n = 1` the formula reads `1 = f(1)`).

**Construction.** The parity subgraph `P n`. With `wt x` the number of ones of `x`, keep the cube
edge `{x, y}` exactly when `wt x + wt y ≡ 1 (mod 4)`. For `y = x + eᵢ` this says that the bits of
`x` other than `i` have even sum, so the rule is symmetric in `x` and `y`.

**Why no square.** In a square with directions `i ≠ j`, write `A = wt x`, `B = wt(x+eᵢ)`,
`C = wt(x+e_j)`, `D = wt(x+eᵢ+e_j)`; each of `B, C` differs from `A` by one, and `D` differs from
`B` by one *in the same direction* as `C` differs from `A` (because `x` and `x+eᵢ` agree in bit
`j`). The four congruences `A+B ≡ A+C ≡ B+D ≡ C+D ≡ 1 (mod 4)` are then contradictory: `omega`
closes each of the four cases.

**Why that many edges.** Double count degrees:
`∑ₓ deg(x) = ∑ᵢ #{x : the edge at x in direction i is kept}`, and for each fixed `i` the map
`x ↦ x + e_j` (any `j ≠ i`, so `n ≥ 2`) is an involution that toggles the keep condition, whence
each inner count is `2ⁿ⁻¹`. So `2·#E = n·2ⁿ⁻¹`. The case `n = 1` is the whole cube `Q₁`.

**Witness.** `n₀ = 6`: `0 → 96`.

## V002 — baseline claude-opus-5 (based on V001)

**Bound.** `f(n) ≥ (n + 1) · 2ⁿ⁻²` for `n ≥ 2`, and `f(n) ≥ n` for `n < 2`. A gain of `2ⁿ⁻²`
over V001 at *every* `n ≥ 2`; exact at `n = 2`.

**Construction.** Fix one direction `l`. Keep **every** edge of the cube in direction `l`, and in
the other `n − 1` directions keep V001's parity half. Equivalently: `Q_n = Q_{n-1} × K₂` with
V001's parity graph in one copy of `Q_{n-1}`, its complement in the other, and the whole perfect
matching between them — the two halves are edge-disjoint, so no square uses two matching edges.

**Why no square.** A square with directions `i ≠ j`. If neither is `l`, all four of its edges are
governed by the parity rule and V001's argument applies verbatim (the proof re-uses
`V001.not_hasSquare`). If one of them is `l`, the square's other two edges are parallel edges in a
direction `≠ l` at `x` and at `x + e_l`, and `V001.keep_flip` says exactly one of those two is
kept.

**Why that many edges.** `∑ₓ deg(x) = 2ⁿ + (n−1)·2ⁿ⁻¹` — direction `l` contributes at every
vertex, each other direction contributes V001's `2ⁿ⁻¹` — so `#E = (n+1)·2ⁿ⁻²`.

**Witness.** `n₀ = 6`: `96 → 112`.

## V003 — baseline claude-opus-5 (based on V002)

**Bound.** V002, patched to the exact values `f(3) = 9` and `f(4) = 24` (V002 gave 8 and 20).
An improvement at two values of `n` only — a small step, taken because the next bound valid for
infinitely many `n` (see below) did not fit in the time left.

**Construction.** Both are the cube with a minimum set of edges deleted so that every square loses
one, found here by exhaustive depth-first search over "delete one of the four edges of the first
square still uncovered": 3 deleted edges in `Q₃`, 8 in `Q₄`, matching `f(3) = 12 − 3` and
`f(4) = 32 − 8`. The graphs are written as `cut n L`, the cube minus a list `L` of edges named by
pairs of binary numerals, and `¬HasSquare` and the edge count are both settled by `decide` on 8
and on 16 vertices — a check of a construction, not a search. The deleted lists are

- `L3 = [(0,1), (2,6), (5,7)]`;
- `L4 = [(0,1), (2,6), (3,11), (4,12), (5,7), (8,10), (9,13), (14,15)]`.

**Witness.** `n₀ = 4`: `20 → 24`.

## V004 — baseline claude-opus-5 (based on V003)

**Bound.** V003, patched at `n = 5` to `55` (V003 gave 48; the true value is `f(5) = 56`).
Again an improvement at one `n` only.

**Construction.** `V003.cut 5 L5`: `Q₅` minus 25 edges meeting all 80 of its squares, so 55 edges
remain. Found by randomised greedy with redundant-deletion pruning, 4000 restarts (the exhaustive
depth-first search that settled `Q₃` and `Q₄` does not reach depth 25). The minimum is 24
deletions (`f(5) = 56`), which this search did not find; an exact-cover/ILP search should.
`L5 = [(0,1),(0,4),(1,9),(2,18),(3,7),(4,5),(6,14),(7,23),(8,10),(9,25),(10,11),(11,27),(12,13),`
`(12,28),(13,15),(16,24),(17,19),(17,21),(18,19),(20,22),(21,29),(24,25),(26,30),(27,31),(30,31)]`.
`¬HasSquare` and the edge count are settled by `decide` on 32 vertices, 73672 heartbeats — the
same `decide` at `n = 6` (64 vertices) would very likely exceed the 200000 budget, so this route
stops here.

**Witness.** `n₀ = 5`: `48 → 55`.

## Values

| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 10 | 16 |
|---|---|---|---|---|---|---|---|---|---|
| `n2ⁿ⁻¹` (all of `Qₙ`) | 1 | 4 | 12 | 32 | 80 | 192 | 448 | 5120 | 524288 |
| V000 (start) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| V001 `n·2ⁿ⁻²` | 1 | 2 | 6 | 16 | 40 | 96 | 224 | 2560 | 262144 |
| V002 `(n+1)·2ⁿ⁻²` | 1 | 3 | 8 | 20 | 48 | 112 | 256 | 2816 | 278528 |
| V003 (V002, patched) | 1 | 3 | **9** | **24** | 48 | 112 | 256 | 2816 | 278528 |
| V004 (V003, patched) | 1 | 3 | 9 | 24 | **55** | 112 | 256 | 2816 | 278528 |
| V005 `max(V004, (2n+3)2ⁿ⁻³)` | 1 | 3 | 9 | 24 | 55 | **120** | **272** | **2944** | 286720 |
| V006 `max(V005, (n+2^⌊log₄n⌋)2ⁿ⁻²)` | 1 | 3 | 9 | 24 | **56** | **128** | **288** | **3072** | **327680** |
| V007 `max(V006, mixed)` | 1 | 3 | 9 | 24 | 56 | **132** | **304** | **3328** | 327680 |
| true `f(n)` | 1 | 3 | 9 | 24 | 56 | 132 | 304–308 | ? | ? |

At `n = 8, 9` (not in the table) V007 gives 672 and 1504; the best known values are 682 (V008,
parked) and 1532, and the search of this session found 7232, 15642, 71800 at `n = 11, 12, 14`
(V007: 7168, 15616, 71680). V007's values at `n = 10, 13, 15, 16, 17, 19` are optimal among
odd-square subgraphs.

## V005 — baseline claude-opus-5 (based on V001, V004)

**Bound.** `record = maxWith V004.record prod3` with `prod3 n = (2n + 3)·2ⁿ⁻³` for `n ≥ 3`
(and `0` below). That is `½(n + 1.5)·2ⁿ⁻¹`: `2ⁿ⁻³` more than V002 at *every* `n ≥ 3`, and it
beats the previous record V004 at every `n ≥ 6` — `n = 6`: 120 > 112, `n = 7`: 272 > 256,
`n = 10`: 2944 > 2816. This is the first version of the track that improves the record at
infinitely many `n`. The `maxWith` keeps V004's exact values at `n = 3, 4, 5`.

**Construction.** The product construction sketched by the previous session, `k = 3`, written
exactly as planned there. Fix three distinct directions `a, b, c : Fin n` (in `valid`, the
coordinates `0, 1, 2`, which exist because `n ≥ 3`). The subgraph is given by a keep-predicate
`kb a b c x i : Bool` on cube edges `{x, x+eᵢ}`:

- `kb … x a = !(!x b && !x c)`  — drop the `a`-edges with `x b = x c = false`;
- `kb … x b = !(x a && x c)`    — drop the `b`-edges with `x a = x c = true`;
- `kb … x c = !(!x a && x b)`   — drop the `c`-edges with `x a = false`, `x b = true`;
- `kb … x i = V001.keep x i` for every other direction `i`.

On the 3-subcube spanned by `a, b, c` this is the optimal 9-edge `C₄`-free `T ⊆ Q₃`, copied on
every coset; outside it is V001's parity half. Each of the three special predicates depends only
on the two special coordinates *other* than its own direction, so `kb` is the same at both ends
of an edge (`kb_flip_self`); for the parity rule this is `keep_symm`. The graph `Q a b c` is
defined by `Adj x y := hammingDist x y = 1 ∧ ∀ i, y = flip x i → (kb x i ∧ kb y i)`, a shape
whose symmetry proof needs no hypothesis on `a, b, c`.

**Why no square.** Let the square run in directions `i ≠ j`.
- `i ∉ {a,b,c}`: the two parallel `i`-edges sit at `x` and `x + e_j`, and `V001.keep_flip` says
  exactly one of them is kept.
- `j ∉ {a,b,c}`: the same with the roles swapped.
- `i, j ∈ {a,b,c}`: three lemmas `no_square_ab`, `no_square_ac`, `no_square_bc`, one per
  unordered pair, each an eight-case check on `x a, x b, x c` after rewriting the four
  keep-values (`cases x a <;> cases x b <;> cases x c <;> simp`). The six ordered cases are
  dispatched by feeding the four hypotheses to the right lemma in the right order; the three
  cases `i = j` contradict `hij`. The directions are matched by `rw [h] at …`, never by `subst`,
  so `a, b, c` keep their names.

**Why that many edges.** `∑ₓ deg x = ∑ᵢ #{x : kb x i}`, and
- `i ∉ {a,b,c}`: `2ⁿ⁻¹`, by `V001.card_keep`;
- `i ∈ {a,b,c}`: `3·2ⁿ⁻²`, the complement of "two named bits have two named values".

The two-coordinate count is the relative halving lemma `card_split`: if `p` is invariant under
flipping bit `j` then `2·#{x : x j = α ∧ p x} = #{x : p x}` (`Finset.card_bij'` with `flip · j`
both ways, plus `Finset.card_filter_add_card_filter_not`). Applied twice it gives
`4·#{x : x p = β ∧ x q = γ} = 2ⁿ` (`card_two`), hence `card_not_two`. Everything is stated as
`4 · (count) = …` so that no natural-number division ever appears. Splitting `∑ᵢ` over
`{a,b,c}` and its complement with `Finset.sum_sdiff` gives
`4·∑ₓ deg x = 3·(3·2ⁿ) + (n−3)·(2·2ⁿ) = (2n+3)·2ⁿ`, so `8·#E = (2n+3)·2ⁿ` and
`#E = (2n+3)·2ⁿ⁻³`.

**Witness.** `n₀ = 6`: `112 → 120`. Cost: 22977 heartbeats in all (limit 200000), heaviest
declaration `card_edges` at 3624 — the whole version is reasoning, with no `decide` over a cube.

## V006 — trial claude-fable (based on V001, V005)

**Bound.** `record = maxWith V005.record bhn` with `bhn n = 2ⁿ·(n + 2^⌊log₄ n⌋)/4`, that is
`(n + 2^⌊log₄ n⌋)·2ⁿ⁻²` for `n ≥ 2`: the Brass–Harborth–Nienborg bound, `½(n + √n)·2ⁿ⁻¹` at
`n = 4ʳ`. It beats V005 at `n = 5` (`56 = f(5)`) and at every `n ≥ 6`; the `maxWith` keeps
`f(3) = 9`. `Nat.log` is fuel-based structural recursion, so the kernel evaluates the record
instantly up to `n = 100`.

**Construction.** A port to this problem's setting of the public Lean formalisation cited in the
literature section. `Col ι` is a colouring `col : (ι → Bool) → ι → Bool` of the edges of the cube
on any index type, well defined on edges and with no all-`true` square (only the `true` class
is required to be square-free, which is all the step needs and admits later base graphs whose
complement has squares). The `Q₄` template is two tables `eDir, oDir : Bool⁴ → Fin 4`; its facts
(`e` and `o` are matchings, are disjoint, and every square has an `e`- and an `o`-edge; each
vertex has `2c + 1` `true` directions) are `decide`d after reducing `∀ v : Fin 4 → Bool` to four
Booleans, about 2300 heartbeats each. `Col.step : Col ι → Col (ι × Fin 4)` is the substitution
step, `Col.extend : Col ι → Col (Option ι)` adds a parity-coloured coordinate, `Col.congr`
transports along `ι ≃ κ`. The tower `Q_{4ʳ}` is `(4ʳ + 2ʳ)/2`-regular at every vertex
(`exists_col_four_pow`), then `t` coordinates are added (`exists_col_add`, a sum formula), and
`n = 4^L + t` is substituted so that no final transport is needed. `Col.graph` is the subgraph
of `HypercubeC4.hypercube n` formed by the `true` edges; `Col.not_hasSquare` and the degree
count feed `le_f_of_not_hasSquare`.

**Witness.** `n₀ = 16`: `286720 → 327680`. Cost: 35098 heartbeats for the whole file.

## V007 — trial claude-fable (based on V006)

**Bound.** `record = maxWith V006.record mixed` with, for `n ≥ 4`, `m = 4ʳ ≤ n < 4ʳ⁺¹`,
`n − m = 3t + d`:

```
mixed n = n·2ⁿ⁻² + (m + t)·2ⁿ⁻²⁻ʳ + [d = 2]·2ⁿ⁻³⁻ʳ   =   (n + (m + t + ½[d = 2])/2ʳ)·2ⁿ⁻².
```

Beats V006 at every `n ≥ 6` except `n = 4ʳ, 4ʳ + 1`: `132 = f(6)`, `304` at `7` (best known),
`672` at `8`, `1504` at `9`, `3328` at `10`, `(19 + 4.25)·2¹⁷` at `19`.

**Construction.** The Brass–Harborth–Nienborg substitution with blocks of mixed sizes. A
*template* `Tmpl k` on `Q_k` is a pair of disjoint edge classes `e`, `o`, well defined on edges,
every square containing an edge of each, with counting data `e j, o j, a j` (numbers of vertices
of a parity class whose `j`-edge is in `e`, in `o`, in neither). Sizes 4 (V006's matchings), 3
(`e = {*00, 0*1, 11*}`, `o = {*10, 1*1, 00*}`), 2 (`e = {*0}`, `o = {*1}`) and 1 (all `a`) are
given, facts by `decide`. `bstep : (∀ w, Tmpl (b w)) → Col ι → Col (Σ w, Fin (b w))` is the
block step (V006's step with per-block templates; its `noSq` proof is V006's verbatim). The
base is the tower `Q₄ → Q₁₆ → …` rebuilt with the block step so that it is regular *in every
direction* (`exists_tower`: `2^(r+1)·D_w = 2^m·(2^r + 1)`); the last level uses the index type
`Fin t ⊕ (Unit ⊕ Fin u)` with sizes `4, d + 1, 1` and is transported to `Fin n` with
`Fintype.equivFinOfCardEq`.

**The count** (`card_bstep`): for a direction `⟨w, j⟩`, with `D_w = #{y | C.col y w}` and
`m = |ι| ≥ 2`, `b ≥ 1`,
`#{X | col X ⟨w, j⟩} = 2^(Σ_{w' ≠ w}(b w' − 1))·((e j + o j)·2^(m−1) + a j·D_w)`.
Proof: the parity outside block `w` is the parity of the other block parities, so the colour is
a function of `(proj X, blk X w)`; curry with `Equiv.piCurry`, split by `proj X = y`
(`Finset.card_eq_sum_card_fiberwise`), split off the block at `w` (`Equiv.piSplitAt`, no casts),
and the rest of the fibre is a product of parity classes (`Equiv.subtypePiEquivPi`,
`Fintype.card_pi`). Then `card_tcol` counts a parity class of the template by colour, and the
outside parity is balanced over `Q_ι`. Three arithmetic lemmas (`arith1/2/3`, one per `d`) turn
the degree sum into `2·mixed n`, by substituting `D = 2ʳ·A + A` with `A = 2^(m−1−r)` and
`2^(3t)·A = 2^(3−d)·2^(n−3−r)`, then `ring`.

**Why this shape is the end of the block-substitution road.** In the substitution, a direction
of excess `x` (`2·density − 1`) replaced by a block with template `T` yields directions of
excess `x·(1 − (E_j + O_j)/2^(k−1))` where `E_j, O_j` are the numbers of `e`-, `o`-edges of
direction `j`; every pair of directions must carry `≥ 2^(k−2)` `e`-edges and as many `o`-edges,
so a block of size 4 or 3 halves the excess of each of its directions (total `2x`, `1.5x`), size
2 gives `(0, x)`, size 1 keeps `x`. So a construction is a tree of blocks and its excess is the
sum of the leaf weights; V007 is the greedy optimum (split the heaviest leaves by size 4, use
the remainder `d` as one block of size `d + 1`), and a template on `Q_k` can never do better
than `f(k)` itself (`multiplier ≤ f(k)/2^(k−2) − k`). It reproduces `f(1..6)` exactly and the
best known `304` at `n = 7`; the only known value it misses is `f(8) ≥ 680` (`672` here).

**Witness.** `n₀ = 7`: `288 → 304`. Cost: 138177 heartbeats for the whole file (heaviest
`card_fibre` 23054, the three `arith` lemmas 12–16k each).

## V008 — trial claude-fable (NOT accepted: parked, see below)

**Bound.** `record = patch V007.record 8 682` (`f(8) ≥ 682`, V007 gives 672).

**Certificate.** Minamoto's 682-edge odd-square witness, as eight 256-bit numbers `M0…M7`
(bit `c` of `Mᵢ` set iff the edge `{c, c ⊕ 2ⁱ}` is kept). `Proof.lean` contains a *generic*
bitmask-certificate module: `code`/`decode` between `Fin n → Bool` and numerals
(`testBit_code`, `code_flip : code (flip x i) = code x ^^^ 2ⁱ`, `card_code`), the popcount `pc`
with `card_testBit_range`, the graph `mgraph M` with `mgraph_not_hasSquare` and
`mgraph_two_mul_card_edges` (from symmetric masks), and the bit-permutation machinery
`A n j` (mask of positions `< 2ⁿ` with bit `j` clear, by doubling), `sw n j M` (bit `c ↦ bit
c ^^^ 2ʲ`, `testBit_sw`), `xor_two_pow_of_testBit_false/true`, so that square-freeness is
`∀ i ≠ j, Mᵢ &&& Mⱼ &&& sw n j Mᵢ &&& sw n i Mⱼ = 0` and symmetry `sw n i Mᵢ = Mᵢ`: `n²` GMP
operations. Everything builds with no `sorry`; 19228 heartbeats in all (the first version, with
a plain `decide` over 256 words × 56 direction pairs, cost 31256 and was also fine for Lean's
kernel).

**Why it is parked.** `squeeze verify` rejects it: *"Comparator exceeded 16384 MB of memory"*
— twice, both with the plain `decide` and with the `sw` formulation, while Lean's own kernel
settles either in well under a second. The common ingredient is `Nat.land`/`Nat.testBit`/shifts
on 256-bit literals; the likely cause is that the replay kernel (nanoda) does not accelerate
the bitwise operations, so `Nat.bitwise` (well-founded recursion) is unfolded on 256-bit
numbers. Not investigated further for lack of context. What to try next, cheapest first:
(i) a certificate using only `+ − × / % ^` (all surely accelerated): `testBit m c` as
`m / 2^c % 2 = 1` (`Nat.testBit_eq_decide_div_mod_eq`), `sw` replaced by the plain
`∀ c < 2ⁿ` check with div/mod (14336 cases at `n = 8` — fine for Lean's kernel, unknown for
nanoda), and `pc` via `% 2` and `/ 2`; (ii) isolate the culprit with tiny fixtures run through
`squeeze verify` (each run takes about 3 minutes); (iii) if bit operations are the problem, a
`List Bool`-free encoding of the graph as a `Fin 256 → Fin 8 → Bool` table would need a
different count argument. The directory `SqueezeBench/Problems/HypercubeC4/Records/Lower/V008/`
(Def, Proof, metadata with witness 8, REPORT) can be reused or rewritten freely since it was
never accepted.

**Search results ready to be patched in** (all odd-square configurations from the simulated
annealing program `ffsa.c` on the fully frustrated model; the masks of finished runs are printed
at the end of each `out_<n>_<seed>.txt`, symmetry/squares/count re-checked in Python):

| n | V007 | found | odd-square bound | files |
|---|---|---|---|---|
| 8 | 672 | 682 | 682 | `masks8.txt` (Lean syntax), used in V008 |
| 9 | 1504 | 1532 | 1536 | `masks9.txt` (Lean syntax, verified: 1532 edges, no square) |
| 11 | 7168 | 7237 | 7296 | 7237 in logs only (`sa/long/log_11_*`); masks at 7232 in `sa/out_11_13.txt` |
| 12 | 15616 | 15642 | 15700 | 15642 in logs only; masks at 15634 in `sa/out_12_*.txt` |
| 14 | 71680 | 71800 | 72362 | 71800 in logs only; masks at 71778 in `sa/out_14_14.txt` |

`n = 10, 13` stay below V007 (as they must). Paths are under the scratch directory
`.lake/scratch/HypercubeC4-Lower/` (`scratch/` for Lean files and masks, `sa/` for the search).
Kernel cost of the `sw` certificate is tiny; the popcount `pc (2ⁿ)` costs about 3.5k heartbeats
per mask at `n = 14`, so one version could carry `n = 9, 11, 12, 14` together once the
comparator issue is solved. `n ≥ 18` is out of reach: 18 masks of 2¹⁸ bits exceed the 1 MB
directory limit and the popcounts the budget.

## What the next improvement would take

**As of V008 (parked).** Solve the comparator memory problem of the bitmask certificate (see
V008's section), then patch in `n = 8, 9` (682, 1532) and, after longer searches, `11, 12, 14`.
The search program (`sa/ffsa.c`, 150 lines of C: Metropolis annealing on the 2ⁿ spins with the
canonical coupling, geometric schedule, greedy descent, restarts) finds the known optimum at
`n = 8` instantly and `1532` at `n = 9` in every 10-minute run; at `n = 11, 12, 14` its values
were still improving after 30 minutes, so parallel tempering or longer runs should gain more.

**As of V007 (trial claude-fable).** The block-substitution method is exhausted (see V007's
section). What remains:

- *Single values by certificate.* `f(8) ≥ 680` (Minamoto 2026, an edge list) against V007's
  672. A cheap kernel certificate for an arbitrary subgraph of `Q_n` given as `n` bitmasks
  `M_i ∈ ℕ` of `2ⁿ` bits (bit `x` of `M_i` = the edge `{x, x ⊕ 2ⁱ}` is kept): `C₄`-freeness is
  `∀ i ≠ j, M_i &&& M_j &&& σ_j M_i &&& σ_i M_j = 0` where `σ_j` moves bit `x` to `x ⊕ 2ʲ`
  (`((M &&& A_j) <<< 2ʲ) ||| ((M >>> 2ʲ) &&& A_j)`, `A_j` the constant mask of positions with
  bit `j` clear), and symmetry is `M_i = σ_i M_i`; all are GMP-accelerated `Nat` operations, so
  `decide +kernel` costs almost nothing even at `n = 9, 10`. The reasoning glue is the bijection
  `(Fin n → Bool) ≃ Fin (2ⁿ)` (`finFunctionFinEquiv`), `testBit` versus `flip`/xor, and the edge
  count as a sum of popcounts. With this, any better small-`n` graph found by search (simulated
  annealing on `Q₉`, `Q₁₀` — V007 gives 1504 and 3328, the averaging upper bounds are 1584 and
  3520) can be patched in.
- *Better templates* only exist where `f(k)/2^(k−2) − k` beats the tree value (`k = 8` is the
  only known case, and it helps at `n = 8` alone).

**As of V006 (trial claude-fable).** The Brass–Harborth–Nienborg tower is in place. The next
step is the mixed-block interpolation described in the literature section: with base `Q_m`,
`m = 4ʳ ≤ n < 4ʳ⁺¹`, and `n − m = 3t + d`, use `t` blocks of size 4, one block of size `d + 1`
and `m − t − 1` blocks of size 1, for `(n + σ)·2ⁿ⁻²` edges with `σ = (m + t + ½[d = 2])/2ʳ`.
This beats V006 at every `n ≥ 6` except `n = 4ʳ, 4ʳ + 1` (`n = 6`: 132; `7`: 304; `8`: 672;
`9`: 1504; `10`: 3328; `19`: `(19 + 4.25)·2¹⁷`). What it needs beyond V006: (i) templates for
block sizes 1, 2, 3 (the size-2 block is the parity extension in disguise and gains nothing; the
size-3 one gains `2ⁿ⁻³⁻ʳ`); (ii) the step over a dependent index type `Σ w, Fin (b w)`, whose
`noSq` and `col_fl` proofs are V006's verbatim; (iii) the *per-direction* count
`#{X | col X ⟨w, j⟩} = 2^{Σ_{w'≠w}(b w' − 1)}·((e + o)·2^{m−1} + a·D_w)`, where `(e, o, a)` are
the template's numbers of `e`-, `o`-, `a`-edge endpoints of direction `j` in each parity class
and `D_w = #{y | C.col y w}`; it follows from `Equiv.piCurry` (`(Σ w, Fin (b w)) → Bool ≃ ∀ w,
Fin (b w) → Bool`), `Finset.card_eq_sum_card_fiberwise` over the block-parity map, and
`Equiv.subtypePiEquivPi` + `Fintype.card_pi` for the fibre sizes, using that the parity outside
block `w` is the parity of the other block parities; (iv) per-direction regularity of the tower
`Q_{4ʳ}` (`D_w = 2^{m−1} + 2^{m−1−r}` for every `w`), by the same count with all blocks of
size 4 from the explicit `Q₄` colouring `qcol v j true false` (12 kept edges per direction).
The pointwise regularity used in V006 is not enough for mixed blocks, because the coefficient of
`C.col (proj X) w` in the degree of `X` depends on the block size of `w`.

Beyond that, better *bases* than `Q_{4ʳ}` (the 132-edge `Q₆`, the 304-edge `Q₇`, the 680-edge
`Q₈` from the literature, all edge lists) would give `s = 2.25, 2.5, 2.625` in place of `2` at
`n = 6, 7, 8` and, through the tower, `s·2ʳ` at `n = 6·4ʳ, 7·4ʳ, 8·4ʳ`; the mixed-block bound from
`Q_{16}` already gives `σ = 4.5` at `n = 24` and `5.25` at `n = 31, 32`, so the gain is small and
each needs a `C₄`-freeness certificate of a 64-, 128- or 256-vertex graph within the budget.

**As of V005 the `k = 3` product construction is done.** The next step is the same scheme with
`k = 4` and the optimal 24-edge `T ⊆ Q₄` listed below: it gives `(n + 2)·2ⁿ⁻²`, i.e. `2ⁿ⁻³` more
than V005 at every `n ≥ 4` (`n = 6`: 128 > 120, `n = 7`: 288 > 272). Concretely, with four
distinct directions `a, b, c, d`, each of the four keep-predicates excludes *two* patterns of
three coordinates instead of one pattern of two, so each special count is `2ⁿ − 2·2ⁿ⁻³ = 3·2ⁿ⁻²`
again while four directions are now special: `2·#E = (n−4)·2ⁿ⁻¹ + 4·3·2ⁿ⁻² = (n+2)·2ⁿ⁻¹`.
Everything in V005 generalises directly — `card_split` applied three times instead of twice
gives the three-coordinate count `8·#{x : x p = β ∧ x q = γ ∧ x r = δ} = 2ⁿ`, and the
"both directions special" check becomes six pair-lemmas on `x a, x b, x c, x d`, each 16 cases
by `cases … <;> simp`. Beyond that, `k = 6` with `f(6) = 132` gives `(4n+9)·2ⁿ⁻⁴`, and
iterating with larger exact values is the Brass–Harborth–Nienborg mechanism towards
`½(n + c√n)·2ⁿ⁻¹`.

The original write-up of the generic step, kept for reference:

The generic step beyond V002 is the product construction that underlies Guan's and
Brass–Harborth–Nienborg's bounds. Split the coordinates into a set `S` of size `k` and the rest.
Keep, in the `n − k` directions outside `S`, V001's parity half of the cube; and in the `k`
directions of `S`, a fixed `C₄`-free subgraph `T ⊆ Qₖ`, copied on every coset of the `S`-subcube.
This is `C₄`-free for any `C₄`-free `T`: a square with both directions outside `S` is V001's case;
a square with one direction outside `S` has its two parallel outside-edges at two words differing
in an `S`-bit, so exactly one of them is kept; a square with both directions in `S` is a square of
`T`. It has

```
(n − k)·2ⁿ⁻² + |T|·2ⁿ⁻ᵏ  edges,   i.e.  (n − k + f(k)/2ᵏ⁻²)·2ⁿ⁻²  at best.
```

`k = 1` (`T` = the one edge of `Q₁`, `f(1) = 1`) is exactly V002. `k = 2` gains nothing.
`k = 3` with `f(3) = 9` gives `(2n+3)·2ⁿ⁻³`, a gain of `2ⁿ⁻³`; `k = 4` with `f(4) = 24` gives
`(n+2)·2ⁿ⁻²`, a gain of `2ⁿ⁻²`; `k = 6` with `f(6) = 132` gives `(4n+9)·2ⁿ⁻⁴`. Since
`f(k)/2ᵏ⁻² − k → ∞` like `2c√k`, iterating this with larger and larger exact values is exactly the
Brass–Harborth–Nienborg mechanism, and it is the route to `½(n + c√n)2ⁿ⁻¹`.

**The obstacle is the edge count, not the `C₄`-freeness.** V001/V002 count edges by
`∑ₓ deg(x) = ∑ᵢ #{x : direction i is kept at x}`, and every inner count is settled by a single
involution (`V001.card_keep`). For `k ≥ 3` the inner count for a direction of `S` is
`#{x : Φ(x|_S)}`, which needs `2ⁿ⁻ᵏ · #{c ∈ Qₖ : Φ(c)}` — a fibre/product argument over
`(Fin n → Bool) ≃ (S → Bool) × (Sᶜ → Bool)`. A workable route, not attempted here for lack of
time: prove the relative halving lemma

> if `Ψ` is invariant under flipping bit `c` and `Φ` is toggled by it, then
> `2·#{x : Ψ x ∧ Φ x} = #{x : Ψ x}`

(a direct generalisation of `V001.card_keep`) and apply it once per coordinate of `S`; with the
explicit `T`s below, every `Φ` that arises is of the form "not (two named bits have two named
values)", so `k` applications of the lemma suffice.

Explicit optimal `T`s found by exhaustive search (delete these edges from `Qₖ`; bits listed low to
high):

- `k = 3`, 9 edges: `{000,100}`, `{010,011}`, `{101,111}`.
- `k = 4`, 24 edges: `{0000,1000}`, `{0100,0110}`, `{1100,1101}`, `{0010,0011}`, `{1010,1110}`,
  `{0001,0101}`, `{1001,1011}`, `{0111,1111}`.

Both are optimal (`f(3) = 9`, `f(4) = 24`) and were checked to meet every square of `Qₖ`.

Other notes:

- `Def.lean` may hold only plain definitions, so the graphs themselves live in `Proof.lean`; only
  the closed-form record function is in `Def.lean`. That costs nothing here.
- The computation budget is not a constraint for this track so far: V001 spends 20208 heartbeats
  in all, V002 7109 and V003 19824, against a limit of 200000. V001 and V002 are pure reasoning;
  V003's two `decide`s cost 3554 (`Q₃`) and 15232 (`Q₄`) heartbeats and V004's one 73672 (`Q₅`);
  the same patch at `n = 6` (`f(6) = 132`, against 112) would need `decide` over 64 vertices,
  roughly 4–8× V004's cost, i.e. over the 200000 limit. Patching by `decide` is out of road.
- A patch at a single `n` is the weakest kind of submission. The product construction described
  above is the one worth writing next: it improves V003 at every `n ≥ k`, and with `k = 4` it is
  `(n+2)·2ⁿ⁻²`, which also re-derives `f(4) ≥ 24` rather than patching it.

## Session note — baseline claude-opus-5 (no new version accepted this session)

No V005 was accepted in this session: the remaining time was spent on the product construction
described above and was not enough to write and verify it. What follows is that construction,
worked out concretely for `k = 3` so that the next submitter can write it straight into Lean;
the mathematics below is checked by hand, not yet by Lean.

**Bound.** `f(n) ≥ (2n + 3) · 2ⁿ⁻³` for `n ≥ 3`, i.e. `½(n + 1.5)·2ⁿ⁻¹`. This is `2ⁿ⁻³` more
than V002 at *every* `n ≥ 3`, and beats the current record V004 at every `n ≥ 6`
(`n = 6`: 120 > 112; `n = 7`: 272 > 256; `n = 3,4,5`: 9, 22, 52, so fold it in with
`maxWith`, do not patch). Fold: `v n = if n < 3 then 0 else (2*n+3) * 2^(n-3)`,
`record = maxWith V004.record v`, witness `n₀ = 6` (`112 → 120`).

**The graph, as keep-predicates.** Write `Kᵢ(x)` for "the cube edge `{x, x+eᵢ}` is kept"; the
whole construction is the family `Kᵢ`, and it must satisfy `Kᵢ(x) = Kᵢ(x+eᵢ)` (an edge has two
ends) and, for every `i ≠ j` and every `x`, `¬(Kᵢ(x) ∧ K_j(x) ∧ Kᵢ(x+e_j) ∧ K_j(x+eᵢ))` (no
square). With `n = m + 3` and the three special directions `0, 1, 2`:

- `K₀(x) = ¬(x 1 = false ∧ x 2 = false)`
- `K₁(x) = ¬(x 0 = true  ∧ x 2 = true)`
- `K₂(x) = ¬(x 0 = false ∧ x 1 = true)`
- `Kᵢ(x) = V001.keep x i` (the parity rule) for `i ∉ {0,1,2}`.

Each of the first three depends only on the two special coordinates *other* than its own
direction, so `Kᵢ(x) = Kᵢ(x+eᵢ)` holds for them by inspection; for the parity rule it is
`V001`'s symmetry. On the 3-subcube this is exactly the optimal 9-edge `T ⊆ Q₃` of the previous
section (the three deleted edges are `{000,100}`, `{101,111}`, `{010,011}`, one per direction).

**Why no square.**
- `i, j ∉ {0,1,2}`: V001's argument (`V001.not_hasSquare`).
- `i ∉ {0,1,2}`, `j` arbitrary `≠ i`: `V001.keep_flip` gives `Kᵢ(x+e_j) ↔ ¬Kᵢ(x)`, so the two
  parallel edges in direction `i` cannot both be kept. This covers every mixed square.
- `i, j ∈ {0,1,2}`: a check on the three bits `x 0, x 1, x 2` only — eight cases, closed by
  `cases hx0 : x 0 <;> cases hx1 : x 1 <;> cases hx2 : x 2 <;> simp_all`. By hand: the square in
  directions `(0,1)` at `x 2 = false` loses its `x 1 = false` edge to `K₀`, and at `x 2 = true`
  its `x 0 = true` edge to `K₁`; directions `(0,2)` lose an edge to `K₀` when `x 1 = false` and
  to `K₂` when `x 1 = true`; directions `(1,2)` lose an edge to `K₂` when `x 0 = false` and to
  `K₁` when `x 0 = true`.

**The edge count.** As in V001, `∑ₓ deg x = ∑ᵢ #{x : Kᵢ(x)}`.
- `i ∉ {0,1,2}`: `2ⁿ⁻¹`, by `V001.card_keep` unchanged.
- `i ∈ {0,1,2}`: `2ⁿ − 2ⁿ⁻² = 3·2ⁿ⁻²`, since the complement fixes two coordinates.

So `2·#E = (n−3)·2ⁿ⁻¹ + 3·3·2ⁿ⁻² = (2n+3)·2ⁿ⁻²` and `#E = (2n+3)·2ⁿ⁻³`.

The only new counting lemma needed is the two-coordinate count
`#{x : x a = α ∧ x b = β} = 2ⁿ⁻²` for `a ≠ b`. Prove it from the halving lemma

> if `p` is invariant under flipping bit `j`, then `2·#{x : x j = α ∧ p x} = #{x : p x}`,

whose proof is `V001.card_keep`'s verbatim (`Finset.card_bij'` with `flip · j` both ways,
plus `Finset.card_filter_add_card_filter_not`); apply it with `p = (x b = β)` and `j = a`,
then with `p = True` and `j = b`.

**After that, `k = 4`.** The same scheme with the optimal 24-edge `T ⊆ Q₄` of the previous
section gives `(n+2)·2ⁿ⁻²`, i.e. `f(5) ≥ 56 = f(5)` and `f(6) ≥ 128`. Its four keep-predicates
each exclude *two* patterns of three coordinates instead of one, so each count is
`2ⁿ − 2·2ⁿ⁻³ = 3·2ⁿ⁻²`... the same `12·2ⁿ⁻⁴`, and the same halving lemma, applied three times
instead of twice, settles it. `k = 3` is the cheaper first step and is what should be written
first.

## Session note — baseline claude-opus-5 (V005 accepted this session)

V005 was written straight from the previous session's worked-out plan; the plan was correct as
stated and needed no mathematical change. The Lean points that cost time, for the next
submitter:

- `SimpleGraph`'s `symm` field is a `Std.Symm` structure, so it takes `⟨fun x y h => …⟩`, not
  `by intro x y h`.
- `rcases hi with rfl | rfl | rfl` on `hi : i = a ∨ i = b ∨ i = c` *eliminates* `a`, `b`, `c`,
  so any later tactic mentioning them by name breaks. Rewrite with `rw [h] at …` instead and
  keep the case analysis in separate lemmas that take `a, b, c` as arguments.
- `Finset.card_sdiff` at this Mathlib pin is the unconditional
  `#(s \ t) = #s - #(t ∩ s)`, with no `t ⊆ s` argument.
- State every count as `c · (count) = …` with `c` the power of two that would otherwise be
  divided out; `omega` then closes the bookkeeping and no `Nat` subtraction appears.
