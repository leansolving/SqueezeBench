# HypercubeC4 — upper track

`f(n) = ex(Qₙ, C₄)`, the largest number of edges in a `C₄`-free subgraph of the `n`-dimensional
hypercube. This is Erdős Problem #86 (open, \$100). `nMin = 1`.

Submitter of the versions below: `baseline claude-opus-5`. Starting record: `V000`, the ambient
bound `C(2ⁿ, 2)`.

## Best known upper bounds (literature)

- **Asymptotic, best known:** edge density at most `0.60318`, i.e.
  `f(n) ≤ (0.60318 + o(1)) · n2ⁿ⁻¹` — Baber, *Turán densities of hypercubes*, arXiv:1201.3587
  (flag algebras). Balogh, Hu, Lidický, Liu, *European J. Combin.* 35 (2014) 75–85 give
  `0.6068 · n2ⁿ⁻¹`. The first bound of this kind is Chung, *J. Graph Theory* 16 (1992) 273–286:
  `(α + o(1)) · n2ⁿ⁻¹` with `α ≈ 0.623` the root of `9α³ + 5α² − 5α − 1 = 0`.
  All three are flag-algebra / entropy arguments out of formalisation reach today.
- **Elementary, valid for every `n`:** `f(n) ≤ ¾ · n2ⁿ⁻¹`. Every square of `Qₙ` must lose an
  edge and every edge lies in `n − 1` squares, so at least `n2ⁿ⁻³` edges are deleted. This is the
  bound V002 formalises (in the equivalent per-direction-pair form, see below).
- **Averaging over subcubes:** `f(n) ≤ ⌊2n · f(n−1)/(n−1)⌋` (OEIS A245762, after Balogh et al.).
  It preserves edge density, so chaining it from `f(2) = 3` reproduces exactly `¾ · n2ⁿ⁻¹`; it
  only bites once a small value *below* `¾` is known. From `f(6) = 132` it gives `f(7) ≤ 308`.
- **Exact values** (OEIS [A245762](https://oeis.org/A245762), offset 1):
  `f(1..6) = 1, 3, 9, 24, 56, 132`; `f(6) = 132` is Harborth and Nienborg, *Bull. ICA* 12 (1994)
  55–60. `f(7) ∈ [304, 308]`. Note `f(n) = ¾ · n2ⁿ⁻¹` exactly for `n = 2, 3, 4`; the elementary
  `¾` bound first loses at `n = 5` (60 against 56).
- **Lower bound for contrast:** `f(n) ≥ ½(n + 0.9√n) · 2ⁿ⁻¹` for `n ≥ 9` — Brass, Harborth,
  Nienborg, *J. Graph Theory* 19 (1995) 17–23. The leading constant is open between `0.5`
  and `0.603`.

## V001 — `f(n) ≤ n · 2ⁿ⁻¹` (baseline claude-opus-5)

**Bound.** `record n = n · 2ⁿ⁻¹`, the number of edges of `Qₙ` itself.

**Idea.** A subgraph of the cube has at most as many edges as the cube
(`f_le_card_edgeFinset_hypercube`), and the cube has `n · 2ⁿ⁻¹` edges. The edge count is the
handshake lemma: the neighbours of a word `x` are exactly its `n` single-bit flips
(`hypercube_adj_iff`, and `flip x` is injective), so every degree is `n` and
`2 · #edges = 2ⁿ · n`.

**Why.** The seed `C(2ⁿ, 2)` ignores the host graph entirely; this is the first bound that uses
it, and it improves the record at every `n ≥ 2` by an exponential factor.

**Witness.** `n₀ = 3`: `28 → 12`.

**Cost.** 3670 heartbeats in all.

## V002 — `f(n) ≤ ¾ · n · 2ⁿ⁻¹` (baseline claude-opus-5, based on V001)

**Bound.** `v n = 3n · 2ⁿ⁻³` and `record = minWith V001.record v`, so
`record n = 3n · 2ⁿ⁻³` for `n ≥ 3` and `record n = n · 2ⁿ⁻¹` for `n ≤ 2`.

**Idea.** Split the edges of a `C₄`-free `G ≤ Qₙ` by direction. Let `A i` be the set of words `x`
whose edge in direction `i` is present in `G`, and `c i = #(A i)`; every edge is counted at both
ends, so `2 · #G.edgeFinset = Σᵢ c i` (handshake plus the fact that a neighbour of `x` in the cube
is a flip of `x`).

The one piece of mathematics is: for `i ≠ j`,

  `2 · (c i + c j) ≤ 3 · 2ⁿ`.

Proof: `c i + c j = #(A i ∪ A j) + #(A i ∩ A j) ≤ 2ⁿ + #(A i ∩ A j)`, and `#(A i ∩ A j) ≤ 2ⁿ⁻¹`
because `x ↦ opp x i j` — flip both bits `i` and `j` — is a fixed-point-free involution that maps
`A i ∩ A j` into its complement: if `x` and `opp x i j` both had their `i`- and `j`-edges present,
the four edges of the square at `x` in directions `i, j` would all be in `G`, which is exactly
`HasSquare G`, ruled out by `free_iff_not_hasSquare`. So `A i ∩ A j` and its image are disjoint
subsets of the `2ⁿ` words.

Summing `2 · (c i + c j) ≤ 3 · 2ⁿ` over all `n(n−1)` ordered pairs of distinct directions gives
`4(n−1) · Σᵢ c i ≤ n(n−1) · 3 · 2ⁿ`, hence `8 · #G.edgeFinset ≤ 3n · 2ⁿ`, i.e.
`#G.edgeFinset ≤ 3n · 2ⁿ⁻³`. Below `n = 3` the bound is read off V001 instead.

This is the classical elementary `¾` bound in a form that never has to count the squares of the
cube: the square-freeness is used once, as an involution argument, and everything else is a
double count over pairs of directions.

**Why.** It improves V001 by a constant factor at every `n ≥ 3`, is the best bound in the
literature that is elementary enough to formalise, and is *exact* at `n = 3, 4`
(`9` and `24`).

**Witness.** `n₀ = 5`: `80 → 60`.

**Cost.** 13065 heartbeats in all (heaviest declaration `main`, 5876).

## V003 — `f(2) ≤ 3` (baseline claude-opus-5)

**Bound.** `record = patch V002.record 2 3`: unchanged everywhere except `record 2 = 3`, which is
the exact value `f(2) = 3`.

**Idea.** `Q₂` has four edges and *is* a square. If a `C₄`-free `G ≤ Q₂` had four edges, then
`G.edgeFinset ⊆ (hypercube 2).edgeFinset` with equal cardinality forces `G = hypercube 2`
(`edgeFinset_inj`, `eq_of_subset_of_card_le`), and `hypercube 2` has the square at `00` in
directions `0, 1`, contradicting `free_iff_not_hasSquare`. The two `decide`s are on `Q₂`, four
vertices, so they cost nothing. The argument is the one sketched for `f 2 = 3` in the problem's
own `Def.lean`.

**Why.** A single point, which the rules discourage — but it is the only value at which the
record was still off from a *known* exact value, and every cheaper general bound (subcube
averaging from `f(2) = 3`) merely reproduces `¾`. The genuinely better general bounds left
(see below) were out of reach in the time available, and the rules prefer a small sound
improvement to stopping early.

**Witness.** `n₀ = 2`: `4 → 3`.

**Cost.** 1043 heartbeats in all.

## V004 — `f(n) ≤ 2ⁿ⁻² + √(2²ⁿ⁻⁴(1 + 2n(n−1)))` (baseline claude-opus-5, based on V002, V003)

**Bound.** `v n = 2ⁿ⁻² + isqrt(2ⁿ⁻²·2ⁿ⁻²·(1 + 2n(n−1)))` and `record = minWith V003.record v`.
Asymptotically `v n = (1/√2 + o(1))·n2ⁿ⁻¹ ≈ 0.7071·n2ⁿ⁻¹`, so it improves V003 at every `n ≥ 5`.

**Idea.** The Kővári–Sós–Turán count inside the cube. With `A i` and `cnt i` as in V002, the
degree of a word `x` is `Σᵢ [x ∈ A i]`, so

  `Σ_x deg(x)² = Σᵢ Σⱼ #(A i ∩ A j) ≤ Σᵢ cnt i + n(n−1)·2ⁿ⁻¹ = 2m + n(n−1)·2ⁿ⁻¹`,

where the off-diagonal terms are bounded by V002's involution lemma `card_inter_le`
(`2·#(A i ∩ A j) ≤ 2ⁿ` for `i ≠ j`) — this is exactly "no two words have two common
neighbours", written per pair of directions. Cauchy–Schwarz
(`sq_sum_le_card_mul_sum_sq`) over the `2ⁿ` words gives `(2m)² ≤ 2ⁿ·Σ_x deg(x)²`, hence with
`t = 2ⁿ⁻²`,  `m² ≤ 2tm + 2t²n(n−1)`, i.e. `(m − t)² ≤ t²(1 + 2n(n−1))`.

**The integer square root.** `Nat.sqrt` is defined by well-founded recursion and does not reduce
in the kernel (`decide` gets stuck on it), so `Def.lean` carries its own `isqrt fuel a`: Newton's
iteration `g ↦ (g + a/g)/2` started at `g = a`, with fuel and an early stop. Only one direction is
needed for soundness — `d·d ≤ a → d ≤ isqrt fuel a` — and it follows from the single step lemma
`d·d ≤ a → d ≤ (g + a/g)/2` for `g ≥ 1`: otherwise `(a/g + 1) + g ≤ 2d`, so
`4·(a/g+1)·g ≤ ((a/g+1)+g)² ≤ 4d² ≤ 4a`, contradicting `a < (a/g+1)·g`. Insufficient fuel can
only make the bound weaker, never unsound; `2n + 16` is ample.

**Why.** It is the first bound below the elementary `¾` that is valid for every `n`, and it beats
V003 at every `n ≥ 5` — infinitely many values — while still being exact at `n = 2, 3, 4`.

**Witness.** `n₀ = 5`: `60 → 59`.

**Cost.** 51218 heartbeats in all (heaviest declaration `main`, 43226).

## V005 — `f(n) ≤ ⌊(2n + 1)·2ⁿ⁻¹/3⌋` (baseline claude-opus-5, based on V002, V004)

**Bound.** `v n = (2n + 1)·2ⁿ⁻¹/3` (floor division) and `record = minWith V004.record v`. The
density is `(2n+1)/(3n) → 2/3 ≈ 0.6667`, below V004's `1/√2 ≈ 0.7071`, and `v` beats V004 at
every `n ≥ 5`.

**Idea.** Sharpen the local input of the V004 count. For `i ≠ j` the cube splits into `2ⁿ⁻²`
squares in directions `i, j`; a square `S` carries `e(S) ≤ 3` edges of `G` (V002), and the
corners of `S` lying in `A i ∩ A j` are exactly the corners of degree `2` inside `S`. A 4-cycle
with `e` edges has at most `e − 1` vertices of degree `2` when `e ≥ 1`, hence at most `⅔·e`
always, which globally is

  **`3 · #(A i ∩ A j) ≤ cnt i + cnt j`**   (`i ≠ j`),

since `Σ_S e(S) = (cnt i + cnt j)/2`. This replaces V004's `2·#(A i ∩ A j) ≤ 2ⁿ`, which came from
the same squares but only used `e(S) ≤ 3`; here the *shape* of the square is used as well.

The inequality is proved without ever mentioning squares. It is equivalent to
`#(A i ∩ A j) ≤ #((A i ∪ A j) \ (A i ∩ A j))`, and the injection is

  `ψ x = if opp x i j ∈ A i ∪ A j then opp x i j else flip x i`.

If `opp x` has an edge it is not in `A i ∩ A j` (V002's involution). Otherwise `flip x i` is in
`A i`, and it cannot be in `A j`: its `j`-edge *is* the `j`-edge of `opp x`. Injectivity on the
two branches is `opp`/`flip` being involutions; the mixed case `opp a = flip b i` forces
`a = flip b j`, so the `i`-edge at `a` is the `i`-edge at `opp b`, putting `opp b` in `A i` and
contradicting the second branch's hypothesis for `b`.

Summing over `j ≠ i` and then over `i` gives `3·Σ_x deg(x)² ≤ (2n + 1)·Σᵢ cnt i`, and
Cauchy–Schwarz over the `2ⁿ` words (`(2m)² ≤ 2ⁿ·Σ deg²`, `Σᵢ cnt i = 2m`) yields
`12m² ≤ 2ⁿ·m·(4n + 2)`, i.e. `3m ≤ (2n + 1)·2ⁿ⁻¹`.

**Why.** It improves V004 at every `n ≥ 5` and by a constant factor of the whole edge count, it
is still exact at `n = 2, 3, 4` (`3, 9, 24` — the inequality chain is tight there), and it uses
only elementary double counting, so the kernel cost stays small.

**Witness.** `n₀ = 5`: `59 → 58`.

**Cost.** 18150 heartbeats in all (heaviest declaration `main`, 14035).

## V006 — `f(n) ≤ min_c ⌊2ⁿ⁻²(n(n−1)(n−2) + 8(c−1)c(c+1)) / (6c(c−1))⌋` (trial claude-fable, based on V002, V005)

**Bound.** `bound n c = 2ⁿ⁻² · (n(n−1)(n−2) + 8(c−1)c(c+1)) / (6c(c−1))` (floor division),
`v n = min_{2 ≤ c ≤ n+2} bound n c` (a structural recursion `best`), `record = minWith V005.record v`.
The best `c` is about `n/∛4`, and `v n = (4^{-1/3} + o(1)) · n2ⁿ⁻¹ ≈ 0.62996 · n2ⁿ⁻¹`, below
V005's `2/3`. It beats V005 at every `n ≥ 5`, is exact at `n = 5` (`56`), and gives `f(6) ≤ 133`,
`f(7) ≤ 306` — below the `308` in the literature (subcube averaging from `f(6) = 132`) — and
`f(8) ≤ 691` (against `704` from averaging `308`).

**Idea: the third moment of the degrees.** `Σ_x C(d(x), 3)` counts pairs `(x, T)`, `T` a set of
three directions all present at `x`. For fixed `T = {i, j, k}` these `x` form
`S = A i ∩ A j ∩ A k` (V002's `A`), and **`4 · #S ≤ 2ⁿ`**: no two elements of `S` differ in
exactly two of the bits `i, j, k` (they would be opposite corners of a full square — V005's
`opp_not_mem`), so `S`, `opp(S, i, j)`, and the images of both under `opp(·, i, k)` are four
pairwise disjoint sets of the size of `S`. Equivalently: a `C₄`-free subgraph of `Q₃` has at
most two vertices of degree `3`. Hence `Σ_x C(d(x), 3) ≤ C(n, 3) · 2ⁿ⁻²`.

**Convexity.** `C(·, 3)` is a convex sequence, so `C(d, 3) ≥ C(c, 3) + C(c, 2)(d − c)` for all
integers `c, d` (proved by induction in both directions from `c`). Summing over the `2ⁿ` words,
with `Σ_x d(x) = 2m`: `2ⁿ C(c,3) + C(c,2) · 2m ≤ 2ⁿ C(c,2) c + C(n,3) 2ⁿ⁻²`, which is
`6c(c−1) m ≤ 2ⁿ⁻² (n(n−1)(n−2) + 8(c−1)c(c+1))`. The secant (rather than the tangent of the
cubic) is exactly the convex hull of the integer sequence, so nothing is lost to integrality;
the choice of `c` is left to the record, which takes the minimum.

**Why.** The previous report's suggestion (higher moments over triples of directions). A
linear program over all 35 local degree profiles `(n₀, n₁, n₂, n₃)` of `C₄`-free subgraphs of
`Q₃` (enumerated outside Lean) shows that no inequality in the `Q₃` degree profile combined
with convexity beats `4^{-1/3}`: at the `Q₃` vertex level this bound is optimal.

**Witness.** `n₀ = 7`: `320 → 306`.

**Cost.** 32579 heartbeats in all (heaviest declaration `main`, 16484). The first draft of
`main` used `nlinarith` and cost 104k; supplying the products of the `choose` identities with
`m` and `2ⁿ⁻²` explicitly and calling `linarith` brought it to 16k.

## V007 — Chung's bound, density `→ (2+√13)/9 ≈ 0.62284` (trial claude-fable, based on V002, V005, V006)

**Bound.** With `psi u = u(5u−4)(u−4)` for `u ≥ 4` (else `0`) and
`W d u = 32·d(d−1)(d−2) + psi u`: `v n = min_{2 ≤ c ≤ n+2} bound n c`, where for
`D = W(c+1, n−c−1) − W(c, n−c) > 0`

    bound n c = ⌊ 2ⁿ⁻¹ · (8n(n−1)(n−2) + c·D − W(c, n−c)) / D ⌋

(and `n·2ⁿ⁻¹` when `D ≤ 0`); `record = minWith V006.record v`. It beats V006 at every
`n ≥ 12` (`n = 12`: `16286 → 16283`; `n = 15`: `160995 → 160651`; `n = 20`:
`6807800 → 6779430`; `n = 100`: density `0.62756`, still far from the limit `0.62284`).
Below `n = 12` the extra term `psi(n − d)` vanishes at the relevant degrees and the record
equals V006.

**Idea (Chung 1992, §4, Lemma 13).** In each `Q₃` block, call a pair of directions `{i, j}`
*blue at a corner `v`* when the two edges of the square `(i, j)` at `v` avoiding `v` are
present. With `h` the number of full corners and `b(v)` the number of blue pairs at an
isolated corner `v`:

    4h + Σ_{v isolated} (b(v) − 1)² ≤ 8 .

(If some isolated `v` has `b = 3`, the far edges form a hexagon; the only other possibly
isolated or full corner is the antipode of `v`, with at most one edge. Otherwise each isolated
corner contributes `≤ 1`, `h ≤ 2`, and two adjacent full corners leave exactly two candidate
isolated corners, each with exactly one blue pair.) Summed over all ordered triples of
directions and all blocks this reads

    32·Σ_x d(d−1)(d−2) + 8·Σ_x Σ_{(i,j,k) ⊆ M_x} (b − 1)² ≤ 8n(n−1)(n−2)·2ⁿ ,

`M_x` the missing directions at `x`. The blue pairs at `x` form a graph on `M_x`
(`t = n − d` vertices, degrees `r_j`), and a double count over ordered triples gives
`Σ_{(i,j,k)} (b−1)² = t(t−1)(t−2) + 6·Σ_j (r_j² − t·r_j/2) ≥ t(t−1)(t−2) − 3t³/8`, i.e.
`8·Σ ≥ psi(t)` for `t ≥ 4`. Hence `Σ_x W(d(x), n−d(x)) ≤ 8n(n−1)(n−2)·2ⁿ`, and the secant of
the convex sequence `d ↦ W(d, n−d)` at `c` (second differences `192d` and `30u−18`) gives
`bound n c` exactly as in V006. Asymptotically `ρ³ + (5/32)(1−ρ)³ ≤ 1/4`, i.e.
`9ρ³ + 5ρ² − 5ρ − 1 ≤ 0`, Chung's cubic.

**Why.** V006 is exactly Chung's Lemmas 4–6 (GPT-6 Astra located this; the `f(7) ≤ 306`
corollary is not stated in the literature, where `f(7) ≤ 308` is quoted). A linear program
over the 828 degree profiles of `C₄`-free subgraphs of `Q₄` (enumerated in C: 1.2·10⁹
subgraphs) shows that `Q₄` vertex-degree profiles alone give only `0.6258` (from the
inequality `n₀ + n₃ + 4n₄ ≤ 16`, equivalently `n₁ + n₂ ≥ 3n₄`), whose proof would need a
long `Q₄` case analysis; Chung's refinement stays in `Q₃`, is provable by hand, and is
better. The block lemma was checked by brute force over the 2902 `C₄`-free subgraphs of `Q₃`
(maximum exactly `8`, 317 tight cases) before writing the proof.

**Formalisation notes.** The block is presented as the eight corners `rel x s`, `s ∈ Bool³`,
of an arbitrary word `x`; since each `s` gives an involution of the cube,
`8·Σ_x g(x) = Σ_s Σ_x g(rel x s) = Σ_x Σ_s g(rel x s) ≤ 8·2ⁿ` (`sum_g_le`) — no fibres, no
distinctness of corners. The case analysis re-bases at the special corner
(`sum_rel_rebase`) and uses invariance under permuting the three directions
(`sum_g_perm12/23`) so that only one adjacent-full-corner case is written out. The
auxiliary-graph identity is done over ordered triples with nested `erase` sums
(`sum_pairs`, `swap_outer`, `aux_bound`); the secant step is a general lemma for convex
sequences in ℕ (`secant`); the arithmetic in `main` is ℕ with `nlinarith`.

**Witness.** `n₀ = 12`: `16286 → 16283`.

**Cost.** 152259 heartbeats in all (heaviest `main` 30648, `main_ineq` 21192,
`sum_g_triples` 18871, `aux_bound` 16434). Boolean AC-normalisation
(`simp only [Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]`) replaced a 1024-case split
that had cost 25k on its own.

## Values

| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 10 |
|---|---|---|---|---|---|---|---|---|
| `n2ⁿ⁻¹` (edges of `Qₙ`) | 1 | 4 | 12 | 32 | 80 | 192 | 448 | 5120 |
| V000 = `C(2ⁿ,2)` (start) | 1 | 6 | 28 | 120 | 496 | 2016 | 8128 | 523776 |
| **V001** = `n2ⁿ⁻¹` | 1 | 4 | 12 | 32 | 80 | 192 | 448 | 5120 |
| **V002** = `¾·n2ⁿ⁻¹` (`n ≥ 3`) | 1 | 4 | 9 | 24 | 60 | 144 | 336 | 3840 |
| **V003** = V002 patched at `n = 2` | 1 | 3 | 9 | 24 | 60 | 144 | 336 | 3840 |
| **V004** = KST inside the cube | 1 | 3 | 9 | 24 | 59 | 140 | 327 | 3700 |
| **V005** = `⌊(2n+1)2ⁿ⁻¹/3⌋` | 1 | 3 | 9 | 24 | 58 | 138 | 320 | 3584 |
| **V006** = third moment, best secant | 1 | 3 | 9 | 24 | 56 | 133 | 306 | 3413 |
| **V007** = Chung's bound (blue pairs) | 1 | 3 | 9 | 24 | 56 | 133 | 306 | 3413 |
| true `f(n)` | 1 | 3 | 9 | 24 | 56 | 132 | 304–308 | ? |

V005 is exact at `n = 1, 2, 3, 4`; the first gap is `n = 5` (58 against 56). Its density
`(2n+1)/(3n) → 2/3 ≈ 0.6667` is below V004's `1/√2 ≈ 0.7071` at every `n ≥ 5`, and below the
elementary `¾` everywhere from `n = 2` on.

V006 is exact at `n = 1, …, 5`; the first gap is `n = 6` (133 against 132). Its density
`→ 4^{-1/3} ≈ 0.62996` is below V005's `2/3` at every `n ≥ 5`. Further values of V006:
`n = 8`: 691, `n = 9`: 1553, `n = 12`: 16286, `n = 15`: 160995 (density 0.655 at `n = 15`; the
finite-`n` density decreases slowly to its limit).

V007 equals V006 for `n ≤ 11` and is strictly below it for every `n ≥ 12`: `n = 12`: 16283,
`n = 13`: 34999, `n = 15`: 160651, `n = 20`: 6779430, `n = 30`: 10283710183 (density
0.6385), `n = 100`: density 0.62756. Its limit density is `(2+√13)/9 ≈ 0.62284`.

## What the next improvement would take (after V007)

- **Below Chung's `0.6228`, still inside `Q₃`.** Balogh–Hu–Lidický–Liu reach `0.6068` with
  edge-rooted square configurations evaluated on the 99 square-free `Q₃` types; a
  hand-provable inequality of that kind (statistics of the `n − 1` squares through an edge,
  squared and expanded, so that only pairs of squares sharing an edge — i.e. `Q₃`
  configurations — appear) is the natural next target. The `Q₃`-block machinery of V007
  (`rel`, `sum_rel_rebase`, `sum_g_le`, `sum_nested_filter`, `sum_triples_const`) is reusable
  for any block inequality summed over all triples of directions.
- **`Q₄` vertex-degree profiles** give at most `0.6258` (LP over all 828 profiles, from
  `n₀ + n₃ + 4n₄ ≤ 16`); weaker than V007 and with a longer proof. Not worth pursuing.
- **Small `n`.** V007 changes nothing below `n = 12`; `f(6) ≤ 133` and `f(7) ≤ 306` stand.
  The exact-`Q₃` LP (integer degrees, third moment plus V005's second-moment bound) does not
  exclude `133` at `n = 6`, so `f(6) = 132` needs a genuinely new local ingredient.
- **Session end (trial claude-fable).** The session was closed by the maintainers right after
  V007 was accepted; no unfinished version is in the tree. Scratch material (the `Q₃`/`Q₄`
  enumerations `q3.py`, `q4.c`, `q4profiles.txt`, the LPs `lp.py`, `lp4.py`, the value tables
  `v7.py`) is under `.lake/scratch/HypercubeC4-Upper/`.

## What the next improvement would take (written after V005)

- **Below `2/3`:** the V005 argument uses, per square, only `3·p(S) ≤ 2·e(S)` where `p(S)` is
  the number of degree-`2` corners. Equality needs every square to have exactly three edges and
  every degree to be the same, which at `n ≥ 5` is already impossible (`¾ > 2/3` in density), so
  there is slack to recover. Making it quantitative means tracking how many squares have `e(S) ≤ 2`
  in terms of the edge density — the natural next step, and the first place where the argument
  stops being purely local.
- **`f(5) ≤ 56` plus subcube averaging** would give `f(n) ≤ 0.7·n2ⁿ⁻¹`, which V005 already beats;
  a `k`-block bound only helps now if `f(k)/(k2ᵏ⁻¹) < 2/3`, and no such exact value is known
  (`f(6)/192 = 0.6875`, `f(7) ≤ 308` would give `0.6875`). `f(8)` is not known.
- **The literature's `0.623` (Chung) and `0.60318` (Baber)** are entropy / flag-algebra
  arguments; no route to a kernel-checked proof is known.

## Earlier notes on the next improvement

- **Below `¾` for all `n`:** the natural next elementary bound is the Kővári–Sós–Turán count
  inside the cube: `Σ_x C(deg x, 2) ≤ #{pairs at Hamming distance 2} = 2ⁿ⁻¹·C(n,2)`, since
  `C₄`-freeness means no pair of words has two common neighbours. With Cauchy–Schwarz this gives
  `f(n) ≤ 2ⁿ⁻²(1 + √(1 + 2n(n−1)))`, i.e. density `→ 1/√2 ≈ 0.7071`. It beats `¾` only for
  moderately large `n` once the integer-`√` rounding is paid for, so it would have to be folded in
  with `minWith`. The formalisation cost is the count of ordered pairs at distance exactly `2`
  (`2ⁿ·C(n,2)`), which is a real Finset computation, plus `Finset.sq_sum_le_card_mul_sum_sq`.
- **Blocks of 5 directions:** `f(n) ≤ (f(5)/80) · n2ⁿ⁻¹ = 0.7 · n2ⁿ⁻¹` would follow from
  `f(5) ≤ 56` by the same per-block double count that V002 uses for pairs (a pair block is a
  `Q₂`, and `f(k)/(k2ᵏ⁻¹)` is `¾` for `k = 2, 3, 4` but `0.7` for `k = 5`). `f(5) ≤ 56` however
  needs an exhaustive search, which the computation budget forbids.
- **The literature's `0.603`** is flag algebras; no route to a kernel-checked proof is known.

**Problems hit.** None that blocked a version. Two notes for whoever comes next: `omega` is
useless on the aggregation step (products of the variable `n` with sums), so the cancellations
have to be done by hand with `Nat.le_of_mul_le_mul_left` and `Nat.le_of_add_le_add_right`; and
`Finset.card_image_of_injOn` wants `Set.InjOn` on the *coercion* of the Finset, not on the Finset.

## Session note (baseline claude-opus-5, short session)

No new version was accepted in this session; the record stands at **V005**,
`f(n) ≤ ⌊(2n + 1)·2ⁿ⁻¹/3⌋` (density `→ 2/3`). What was ruled out, so the next submitter does not
repeat it:

- **Subcube averaging chained from the record itself never bites.** `⌊2n·V005(n−1)/(n−1)⌋` was
  computed against `V005(n)` for `n = 2..12`: it is equal at `n = 3, 4` and strictly *worse*
  everywhere else (`n = 5`: 60 vs 58; `n = 6`: 139 vs 138; `n = 10`: 3602 vs 3584). The averaging
  step preserves density up to rounding, so it can only help from an exact value with density
  below `2/3`, and none is known (`f(6)/192 = 0.6875`).
- **Mixing V002's `2·#(Aᵢ ∩ Aⱼ) ≤ 2ⁿ` back into the V005 count gives nothing.** Taking
  `#(Aᵢ ∩ Aⱼ) ≤ α·2ⁿ⁻¹ + (1−α)(cntᵢ + cntⱼ)/3` and redoing Cauchy–Schwarz yields the limiting
  density `c` with `c² = α/2 + 2c(1−α)/3`, minimised at `α = 0` (`c = 2/3`). At the V005 optimum
  the cnt-based bound is `(4/9)·2ⁿ` against the cardinality bound's `(1/2)·2ⁿ`, so the latter is
  never active.
- **The slack in V005 is not recovered by the obvious integrality refinement.** Writing
  `Σ_S p(S) ≤ E − Z` with `E = Σ_S e(S) = (cntᵢ + cntⱼ)/2` and `Z = #{S : e(S) ≥ 1}`, the only
  available lower bound is `Z ≥ E/3`, which reproduces `p ≤ 2e/3` exactly. Turning the slack into
  a gain needs a bound on `Z` that depends on the global edge density — i.e. showing that a dense
  `C₄`-free subgraph must have many squares with `e(S) ≤ 2`. That remains the natural next step,
  as recorded above.
- **Higher moments over triples of directions** look like the first genuinely new ingredient: in a
  `Q₃` block a `C₄`-free subgraph with the maximum 9 edges has only 2 vertices of degree 3
  (the 3 deleted edges are disjoint and cover 6 of the 8 corners), a ratio of `2/9` against the
  pairwise `2/3`. A power-mean inequality on `Σ_x C(deg x, 3)` fed by such a triple bound is the
  most promising elementary route below `2/3`, but it needs the `Q₃` case analysis formalised,
  which does not fit a short session.
