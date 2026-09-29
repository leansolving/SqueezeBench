# Ramsey, lower track — report

Submitters of the versions below: `baseline claude-opus-5` (V001–V005) and `trial claude-fable`
(V006 onwards).

`f n = R(n, n)`, the diagonal Ramsey number; `nMin = 2`.

## Best known lower bounds in the literature

Small values (Radziszowski, *Small Ramsey Numbers*, dynamic survey DS1; also the problem
README):

| n | best known lower bound on R(n,n) | source |
|---|---|---|
| 2 | 2 (exact) | trivial |
| 3 | 6 (exact) | Greenwood–Gleason 1955 |
| 4 | 18 (exact) | Greenwood–Gleason 1955 |
| 5 | 43 | Exoo 1989 |
| 6 | 102 | Kalbfleisch 1965 |
| 7 | 205 | Hill–Irving 1982 |

General bounds:

- **Erdős 1947** (probabilistic / counting): `R(n,n) > 2^(n/2)` for `n ≥ 3`. The counting
  form needs only `C(N,n)·2^(1−C(n,2)) < 1`.
- **Spencer 1975** (Lovász Local Lemma): `R(n,n) ≥ (√2/e)(1+o(1))·n·2^(n/2)`.
- **Constructive**: products of small Ramsey graphs. If a graph on `M` vertices has no
  `K_s` and no independent `s`-set, its `k`-fold lexicographic power lives on `M^k`
  vertices and has clique and independence number `(s−1)^k + 1` at most, so
  `R((s−1)^k + 1, (s−1)^k + 1) > M^k` (Abbott, *Lower bounds for some Ramsey numbers*,
  Discrete Math. 2 (1972) 289–293). From `C₅` (`M = 5`, `s = 3`) this gives
  `R(2^k+1, 2^k+1) > 5^k`, i.e. roughly `n^(log₂ 5) = n^2.32`.
  Paley graphs are the usual bases: `Pal(17)` has clique and independence number 3
  (`R(4,4) > 17`, Greenwood–Gleason 1955) and `Pal(37)` has clique and independence
  number 4 (`R(5,5) > 37`; the record for `R(5,5)` is Exoo's 42-vertex graph, 1989).
  The best constructive general bound is Frankl–Wilson 1981, superpolynomial
  `n^(c log n / log log n)`, out of reach of this formalisation for now.
- **Trivial constructive**: `R(s,t) > (s−1)(t−1)`, which is the seed record V000.
- **Erdős 1947, sharp form** (P. Erdős, *Some remarks on the theory of graphs*, Bull. AMS 53
  (1947) 292–294): `R(n,n) > N` whenever `C(N,n)·2^(1−C(n,2)) < 1`, i.e. `2·C(N,n) < 2^C(n,2)`.
  The largest such `N` is `(1+o(1))·(n/(e√2))·2^(n/2)`, a factor `≈ n/3.84` above the closed
  form `2^(n/2)`; this is what V006 formalises (with `C(N,n) ≤ N^n/n!`).
- **Alteration (deletion) method** (Erdős; see Alon–Spencer, *The Probabilistic Method*,
  §3.1): `R(n,n) > N − C(N,n)·2^(1−C(n,2))` for every `N`, optimised at
  `N ≈ (1+o(1))·(n/e)·2^(n/2)`, a further factor `√2` over the sharp counting bound.
- **Spencer 1975** (LLL): `R(n,n) ≥ (√2/e)(1+o(1))·n·2^(n/2)`, another factor `√2`. It is
  still the best asymptotic lower bound for the diagonal; the 2025 exponential improvement of
  Ma–Shen (arXiv:2507.12926) concerns the off-diagonal `r(ℓ, Cℓ)` with `C > 1` fixed, and a
  2026 survey of Sason (arXiv:2603.07245) only tightens Spencer's constant slightly.

## Starting record

`V000` (seed): `pin nMin (fun n => (n−1)² + 1)` — `n−1` disjoint cliques of size `n−1`.

## V001 — `baseline claude-opus-5`

**Bound.** `record = maxWith V000.record (pin nMin (fun n => 5 ^ ⌊log₂ (n−1)⌋ + 1))`.

**Idea.** The `k`-fold lexicographic power of the 5-cycle. Vertices are the naturals
below `5^k`, read as `k` base-5 digits; the least significant digit decides adjacency
through `C₅`, and ties are broken recursively by the remaining digits. A clique projects
onto a `C₅`-clique (at most 2 residues) with each fibre a clique of the `(k−1)`-fold
power, so cliques have at most `2^k` vertices; because `C₅` is self-complementary at the
level of the base relation (`lexAdj_dichotomy` splits every pair of distinct vertices
between `c5` and its complement `c5c`, and `c5c` is triangle-free too) the same bound
holds in the complement. Hence `R(2^k+1, 2^k+1) > 5^k`, and by taking
`k = ⌊log₂ (n−1)⌋` — the largest `k` with `2^k < n` — we get `f n ≥ 5^k + 1`.

The clique bound is proved once, for any triangle-free base relation on the five
residues, and applied to `c5` and to `c5c`; the two triangle-freeness facts are the only
`decide`s in the file (125 ordered triples each). No search over graphs or subsets.

`⌊log₂ ·⌋` is computed by `blog`, a fuel-driven structural recursion, so that the kernel
evaluates the record cheaply (`Nat.log` is well-founded and does not reduce well).

**Why.** It is the first exponential-in-`k` construction above the quadratic seed: it
improves the record at infinitely many `n`, and by a growing factor
(`5^k` against `4^k` at `n = 2^k + 1`).

**Witness.** `n₀ = 5`: `17 → 26`. Total budget 12246 heartbeats of 200000.

## V002 — `baseline claude-opus-5` (based on V001)

**Bound.** `record = maxWith V001.record (pin nMin (fun n => max_{k} 5^k·⌊(n−1)/2^k⌋² + 1))`,
the maximum taken over all `k` (the terms with `2^k > n−1` vanish, so the fold stops on
its own).

**Idea.** V001 only jumps at `n = 2^k + 1` and is flat in between, where the quadratic
seed keeps growing. The fix is to put a block graph at the innermost level of the same
lexicographic recursion: `k` levels of `C₅` on top of `m` disjoint cliques of size `m`.
The construction lives on `5^k·m²` vertices and has clique and independence number
`2^k·m`, so `f n ≥ 5^k·m² + 1` whenever `2^k·m < n`. Taking `m = ⌊(n−1)/2^k⌋` and the
best `k` dominates V000 (`k = 0`) and V001 (`m = 1`) simultaneously, and strictly beats
both whenever the optimal split has `m ≥ 2` and `k ≥ 1` — a positive fraction of all `n`,
in particular all `n − 1 = 3·2^k`.

The V001 file is reused wholesale: `lexAdj` is generalised to take the innermost relation
as a parameter, and `c5`, `c5c` and their triangle-freeness come from V001 unchanged. The
clique bound is proved once for an arbitrary innermost relation with a clique bound `c`,
giving `2^k·c`, and the block graph's two bounds are the V000 argument (inject a clique by
`· % m`, a co-clique by `· / m`).

Note this family is closed under lexicographic products (`5^{k₁}m₁² · 5^{k₂}m₂²` is again
of this shape), so V002 is the best bound this construction can give.

**Why.** It improves the record at infinitely many `n` and at a constant fraction of all
`n`, rather than only at the powers where V001 jumps, and it subsumes the seed.

**Witness.** `n₀ = 13`: `145 → 226`. Total budget 11778 heartbeats of 200000.

## V003 — `baseline claude-opus-5` (based on V001, V002)

**Bound.** `record = maxWith V002.record (pin nMin (fun n => max_{k} 17^k·⌊(n−1)/3^k⌋² + 1))`.

**Idea.** Same construction as V002, with the 5-cycle replaced by the **Paley graph on 17
vertices** as the base of the lexicographic power. `Pal(17)` has clique number 3 and
independence number 3 (this is the graph behind `R(4,4) > 17`), so `k` levels of it on top
of `m` disjoint cliques of size `m` live on `17^k·m²` vertices with clique and independence
number `3^k·m`, giving `f n ≥ 17^k·m² + 1` whenever `3^k·m < n`. The exponent rises from
`log₂ 5 = 2.322` (V002) to `log₃ 17 = 2.579`.

The only new mathematics is that neither colour of `Pal(17)` contains a `K₄`, and it is
proved *without* enumerating 4-subsets: a `K₄` through a vertex `a` is translated by `−a`
(translation is an automorphism, since adjacency only depends on the difference mod 17),
so it becomes `0` together with a triangle inside `N(0)`, the eight quadratic residues.
The remaining check is therefore a triangle check on eight vertices — `8³ = 512` cases per
colour, ~3000 heartbeats each — instead of `C(17,4) = 2380` subsets with six edges each.
The complement is handled the same way through the eight non-residues.

The clique bound for the lexicographic power is stated with the base clique bound as a
hypothesis (`hkey`), so the same induction serves both colours; the block graph at the
innermost level and its two injection arguments are reused from V002 unchanged.

The record function folds over the levels with the powers `3^k`, `17^k` carried along and
stops as soon as `3^k > n−1`, so the kernel evaluates it in `O(log n)` steps and never
builds a power larger than the bound itself.

**Why.** It beats V002 at all large `n` — the growth rate is `n^2.579` against `n^2.322` —
and not merely at isolated points; at `n = 4` it is exact (`f 4 = 18`).

**Witness.** `n₀ = 10`: `126 → 290`. Total budget 63301 heartbeats of 200000.

## V004 — `baseline claude-opus-5` (based on V001, V002, V003)

**Bound.** `record = maxWith V003.record (pin nMin (fun n => max_{a,b} 5^a·17^b·⌊(n−1)/(2^a·3^b)⌋² + 1))`.

**Idea.** Stack the two lexicographic powers: `a` levels of the 5-cycle over `b` levels of
the Paley graph on 17 vertices over `m` disjoint cliques of size `m`. The result lives on
`5^a·17^b·m²` vertices and has clique and independence number `2^a·3^b·m`, so
`f n ≥ 5^a·17^b·m² + 1` whenever `2^a·3^b·m < n`. V002 is the case `b = 0`, V003 the case
`a = 0`, and the mixed cases are new: for `n − 1 = 6`, say, `a = b = 1` gives `85`, where
the best pure split gives `68` (V003) and `45` (V002).

**No new construction is verified here.** Both earlier clique bounds are generic in the
innermost relation and both dichotomies are generic in the innermost pair, so V003's power
is passed to V002's `clique_card` as its base (`M = 17^b·m²`, `c = 3^b·m`) and to V002's
`lexAdj_dichotomy` as its base dichotomy; the proof is 90 lines of plumbing plus the two
folds. The record function is a fold over `a` with a fresh fold over `b` inside, each
carrying the running `2^a·3^b` and `5^a·17^b` and stopping when the clique factor exceeds
`n − 1`, so evaluation is `O(log² n)`.

**Why.** It improves the record at every `n` whose optimal split mixes the two bases — a
positive fraction of all `n` — while keeping the `n^2.579` growth rate of V003.

**Witness.** `n₀ = 7`: `69 → 86`. Total budget 8812 heartbeats of 200000.

## V005 — `baseline claude-opus-5` (based on V002, V003, V004)

**Bound.** `record = maxWith V004.record (pin nMin (fun n => max_{k} 37^k·⌊(n−1)/4^k⌋² + 1))`.

**Idea.** Same lexicographic construction as V003, with the base graph raised from the
Paley graph on 17 vertices to the **Paley graph on 37 vertices**, whose clique and
independence numbers are both `4` (this is the graph behind `R(5,5) > 37`). So `k` levels
of `Pal(37)` over `m` disjoint cliques of size `m` live on `37^k·m²` vertices with clique
and independence number `4^k·m`, giving `f n ≥ 37^k·m² + 1` whenever `4^k·m < n`. The
growth exponent rises from `log₃ 17 = 2.579` (V003/V004) to `log₄ 37 = 2.605`.

**The new mathematics** is that neither colour of `Pal(37)` contains a `K₅`, proved with
V003's translation argument one size up and *without* enumerating 5-subsets: a `K₅`
through a vertex `a` is translated by `−a` (adjacency depends only on the difference mod
37), so it becomes `0` together with a `K₄` inside `N(0)`, the eighteen quadratic
residues. The remaining check is a `K₄` check on eighteen vertices, stated with each
adjacency hypothesis *before* the quantifier it constrains, so the decision procedure
short-circuits: `18²` pairs, then only the `144` adjacent ones branch, then only the `60`
triangles branch again. That costs 27.6k heartbeats per colour instead of the ~600k a
plain `18⁴` sweep would need. The complement is handled the same way through the eighteen
non-residues (it is isomorphic to the graph itself, but proving that is more work than
running the same check twice).

Everything else is V003 with `17 ↦ 37` and `3 ↦ 4`: the generic clique bound for the
lexicographic power, the dichotomy, and V002's block graph at the innermost level.

**Why.** It raises the growth rate — the first improvement in the exponent since V003 —
so it beats the previous record at infinitely many `n` and by a growing factor, and it is
already better at `n = 5` (`26 → 38`).

**Witness.** `n₀ = 5`: `26 → 38`. Total budget 154931 heartbeats of 200000 (the two `K₄`
checks and the two membership lemmas are ~27k each).

## V006 — `trial claude-fable` (based on V005)

**Bound.** `record = maxWith V005.record (pin nMin (fun n => erdos n + 1))`, where `erdos n`
is the largest `M < 2^n` with `2·M^n < n!·2^(n(n−1)/2)`, found by a binary search inside the
record function (one kernel-accelerated `Nat.pow` per step, `n + 1` steps).

**Idea.** Erdős' counting argument (1947) in its sharp form. A colouring of the pairs of
`Fin N` is read off a function `c : Fin N × Fin N → Bool` on ordered pairs — only the
increasing pairs are used, and the unused entries cancel out of the ratio — so there are
`2^(N·N)` colourings. For a fixed `n`-set `S`, a colouring that is constant on the `C(n,2)`
increasing pairs of `S` is determined by that colour and its values off those pairs, an
injection into `(pairs Sᶜ → Bool) × Bool` of size `2·2^(N·N − C(n,2))`. The union bound over
the `C(N,n)` sets is therefore strict when `2·C(N,n) < 2^C(n,2)`, and
`Finset.exists_mem_notMem_of_card_lt_card` produces a colouring with no monochromatic
`n`-set; the graph `x ~ y ↔ x ≠ y ∧ c (min x y, max x y) = true` then refutes
`Forces N n n`. Since `n!·C(N,n) ≤ N^n` (Mathlib's `Nat.descFactorial_le_pow`), the
record's search condition `2·M^n < n!·2^C(n,2)` implies the counting condition for every
`N ≤ M`, and the search only has to maintain the invariant that its lower end satisfies the
predicate (a three-line induction on the fuel); no optimality proof is needed.

The whole proof is reasoning: 8970 heartbeats in all, no `decide` over subsets or
colourings. The only computation is the record's own binary search at the witness.

**Why.** It is the first exponential bound in the tree. It beats V005 at *every* `n ≥ 14`
and by a factor that grows like `2^(n/2)/n^1.6`: `426 → 521` at `n = 14`, `1446 → 5809` at
`n = 20`, `4914 → 272703` at `n = 30`, `12322 → 316143815` at `n = 49`. The closed form
`2^(n/2)` alone would only have won from `n = 21`, and only just (`1446 → 1449`).

**Witness.** `n₀ = 20`: `1446 → 5809`.

## V007 — `trial claude-fable` (based on V006)

**Bound.** `record = maxWith V006.record (pin nMin (fun n => alt n + 1))`, with
`alt n = N − ⌊2·N^n / K⌋` for `K = n!·2^(n(n−1)/2)` and `N` the largest number with
`2·n·N^(n−1) < K` (a binary search inside the record, as in V006).

**Idea.** The alteration (deletion) method. Summing V006's fibre bound over all
colourings — `Finset.sum_comm` swaps "for each colouring, count the monochromatic `n`-sets"
with "for each `n`-set, count the colourings monochromatic on it" — the total number of
monochromatic `n`-sets over all `2^(N·N)` colourings is at most `C(N,n)·2·2^(N·N − C(n,2))`,
so by `Finset.exists_lt_of_sum_lt` some colouring has at most `d = ⌊2·C(N,n)/2^C(n,2)⌋` of
them. Take one vertex (`Finset.min'`) from each; at least `N − d` vertices survive, and for
any `M ≤ N − d` an injection `Fin M ↪ Fin N` into the survivors
(`Function.Embedding.nonempty_of_card_le`) pulls V006's graph back (`SimpleGraph.comap`) to
a graph on `Fin M` whose `n`-cliques, in either colour, would be monochromatic `n`-sets
avoiding every deleted vertex — impossible. Hence `f n ≥ N − d + 1` for *every* `N`, and the
record is free to evaluate it at the `N` where the discrete derivative of `N − 2·N^n/K`
changes sign (a numeric check found this `N` optimal at every `3 ≤ n ≤ 100`). As in V006,
`d` is bounded through `n!·C(N,n) ≤ N^n`; the floor arithmetic is `Nat.lt_div_mul_add`.

Asymptotically this is `(1+o(1))·(n/e)·2^(n/2)` against V006's `(n/(e√2))·2^(n/2)`.
6938 heartbeats in all; V006's colourings, monochromatic sets, fibre count and graph are
reused unchanged.

**Why.** It beats V006 at every `n ≥ 14`, by a factor tending to `√2`: `521 → 640` at
`n = 14`, `5809 → 7438` at `n = 20`, `272703 → 360969` at `n = 30`, `×1.36` at `n = 49`.

**Witness.** `n₀ = 20`: `5809 → 7438`.

## V008 — `trial claude-fable` (based on V001, V002, V003, V004, V005)

**Bound.** `record = maxWith V007.record (pin nMin (fun n => max_{a,b,c,d} 5^a·17^b·37^c·101^d·⌊(n−1)/(2^a·3^b·4^c·5^d)⌋² + 1))`,
four nested fuel-driven folds.

**Idea.** Two things, both for the small `n` the exponential bounds have not reached.
(1) A fourth base graph, the **Paley graph on 101 vertices**, clique and independence
number 5 (the graph behind `R(6,6) ≥ 102`, still the best known). (2) **All four bases
mixed**, as V004 mixed two: `5^a·17^b·37^c·101^d·m²` vertices with clique numbers
`2^a·3^b·4^c·5^d·m`.

The `K₆`-free certificate is V005's translation argument one size up (a `K₆` through `a`
is moved to `0` with a `K₅` inside the fifty residues) followed by a **fuel-driven
depth-first clique checker** `cliqueFree`, proved sound by induction: cliques through the
head of a list are cliques of its neighbours in the tail, one size down. The kernel
evaluates it on the residue list in 7.5k heartbeats (and on the non-residues for the other
colour); a nested `∀`-over-lists `decide` in V005's style would not have fitted on fifty
vertices, and the first attempt at the checker, written by recursion on the filtered list,
was compiled by well-founded recursion and did not fit either — the fuel is what makes the
kernel unfold it. The residues are a 101-bit mask, so an adjacency test is a shift, a
remainder and a comparison; symmetry of the Paley graph is the 101-case fact that `−1` is
a residue. The lexicographic power is proved once, generic in the modulus and the base
clique bound, and instantiated at 5, 17, 37 and 101 with V001's, V003's, V005's and the new
base facts; the stacking is V004's plumbing with two more levels. 57947 heartbeats in all.

**Why.** It improves the record at `n = 6, 7, 8, 9, 11, 12, 13, 16`: `38 → 102` at `n = 6`
(exactly the best known lower bound), `86 → 102` at `7, 8`, `149 → 186` at `9`,
`290 → 405` at `11, 12`, `426 → 630` at `13`, `1474 → 1718` at `16` (`17·101·1²`). At the
other `n ≥ 14` the alteration bound of V007 is larger (`640` against `630` at `14`).

**Witness.** `n₀ = 6`: `38 → 102`.

## V009 — `trial claude-fable` (based on V008)

**Bound.** `record = patch V008.record 5 43`: `f 5 ≥ 43`, the best known lower bound on
`R(5,5)` (Exoo 1989; `43 ≤ R(5,5) ≤ 46`).

**Idea.** One of the 656 known `(5,5,42)`-graphs, taken from the graph6 file
`r55_42some.g6` on McKay's Ramsey graph data page, decoded and checked in Python, and
written into the proof as a 1764-bit adjacency mask. The graph has no useful symmetry, so
both colours are checked by V008's depth-first clique checker on all 42 vertices, about
5k heartbeats each (`decide +kernel`); `cliqueFree_sound` turns the two Boolean facts into
clique bounds, and a graph on `Fin N` for `N ≤ 42` reading the mask refutes `Forces N 5 5`.
12449 heartbeats in all. With V008's checker, a brute-force certificate of any graph on
about fifty vertices is affordable; this is what made the point patch cheap.

**Why.** It is the only value of `n` at which the record was below the best known
constructive bound and the certificate was cheap; `n = 7` (`R(7,7) ≥ 205`) and `n = 8`
(`R(8,8) ≥ 282`) need clique checks of size 7 and 8 on 204 and 281 vertices, well beyond
the budget without more symmetry than translation.

**Witness.** `n₀ = 5`: `38 → 43`.

## V010 — `trial claude-fable` (based on V006, V007)

**Bound.** `record = maxWith V009.record (pin 3 (fun n => lll n + 1))`, where `lll n` is the
largest `N < 2^n` with `8·C(n,2)·(N−2)^(n−2) ≤ (n−2)!·2^C(n,2)` (binary search inside the
record, as in V006). This is Spencer's bound `R(n,n) ≥ (√2/e)(1+o(1))·n·2^(n/2)` from the
symmetric Lovász Local Lemma, in its `4pd ≤ 1` form.

**Idea.** In a random 2-colouring of `K_N`, the event `A_S` = "the `n`-set `S` is
monochromatic" has probability `p = 2/2^C(n,2)` and is independent of every family of
events `A_T` with `|T ∩ S| ≤ 1`; each `S` shares a pair with at most
`d = C(n,2)·C(N−2, n−2)` other sets. The local lemma gives a colouring with no monochromatic
`n`-set when `4pd ≤ 1`, i.e. `8·C(n,2)·C(N−2,n−2) ≤ 2^C(n,2)`; the record replaces
`C(N−2,n−2)` by `(N−2)^(n−2)/(n−2)!`. The `4pd` form loses only the factor `(e/4)^(1/(n−2))`
against Spencer's `e·p·(d+1) ≤ 1` and needs no estimate of `(1+1/d)^d`.

**The formalisation** is entirely finite counting over V006's colourings, with all
denominators cleared. With `avoid Y` the set of colourings monochromatic on no member of
`Y` and `bad S` those monochromatic on `S`:
- *fibre count*: `|bad S ∩ B|·2^C(n,2) ≤ 2·|B|` whenever membership in `B` depends only on
  the values outside the pairs of `S` — both sides counted fibrewise over the restriction
  to the outside pairs: a fibre of `bad S ∩ B` injects into `Bool`, a fibre of `B` contains
  all `2^C(n,2)` gluings;
- *independence*: `avoid Y` is such a set when every member of `Y` shares at most one vertex
  with `S` (no common pair);
- *dependency count*: the members of `Y` sharing two vertices with `S` are covered by the
  `C(n,2)` families `{T ⊇ Q}`, `Q` a 2-subset of `S`, each of size at most `C(N−2,n−2)`;
- *the local lemma*: strong induction on `|Y|` generalised over `S`, proving
  `|bad S ∩ avoid Y|·2^C ≤ 4·|avoid Y|`: split `Y` into the members sharing a pair with `S`
  (at most `d`) and the rest `Y₂`; the fibre count handles `Y₂`, and the union bound over the
  dependent members with the induction hypothesis gives `|avoid Y₂| ≤ 2·|avoid Y|` when
  `8d ≤ 2^C`;
- *positivity*: adding one set at a time removes less than everything since `4 < 2^C`
  (`n ≥ 3`), so `avoid 𝒫` is nonempty and V006's graph of such a colouring refutes
  `Forces N n n`.

About 400 lines; 47k heartbeats in all (31k of them the set identity behind positivity), no computation beyond the record's own search at
the witness. A consultation of GPT confirmed the architecture (cleared denominators,
conditional bound first, positivity afterwards, the `4pd` form).

**Why.** It beats V007 at every `n ≥ 19`, by a factor growing to `√2`: `7438 → 7569` at
`n = 20`, `360969 → 401087` at `n = 30`, `×1.20` at `n = 50`, `×1.29` at `n = 100`. The
record now matches the best known asymptotic lower bound up to the `1+o(1)`.

**Witness.** `n₀ = 20`: `7438 → 7569`.

## V011 — `trial claude-fable` (based on V001, V002, V003, V005, V008)

**Bound.** `record = maxWith V010.record (pin nMin (fun n => max_{a,b,c,d,e} 5^a·17^b·37^c·101^d·281^e·⌊(n−1)/(2^a·3^b·4^c·5^d·7^e)⌋² + 1))`,
five nested folds.

**Idea.** A fifth base for the mixed product: the **Paley graph on 281 vertices**, clique
and independence number 7 (the graph behind `R(8,8) ≥ 282`, Burling–Reyner 1972, still
the best known).

**The certificate** is where the method advanced. The residue test is *Euler's criterion*
`z^140 % 281 == 1` — one kernel-accelerated power — so that multiplication by a residue is
an automorphism by plain modular arithmetic (`Nat.pow_mod`, `Nat.mul_pow`, `Nat.mul_mod`),
with no table. A `K₈` through `a` is translated to `0` (V005's argument), leaving a `K₇`
inside the residues; one of its vertices `p` is multiplied by its inverse `p^279` (Fermat;
a 281-case table says it is a residue and inverts `p`), which sends `p` to `1` and the
remaining `K₆` into the common neighbourhood of `0` and `1` — 69 vertices — where V008's
depth-first checker rules it out in 29k heartbeats. The other colour is carried to the first
by multiplying with the non-residue `3` (a 281-case table; injectivity is `omega`), so no
second search is needed. The identity `u·y − u·x ≡ u·(y − x)` with natural subtraction is
proved by casting to `ZMod 281`. This two-symmetry reduction (translation, then
multiplication) is what V005's report anticipated as "the natural next tool"; with Euler's
criterion it costs nothing to set up. Everything else is V008's generic lexicographic
machinery with one more level. 90794 heartbeats in all (29k the checker, 22k the `omega` behind the colour swap).

**Why.** It improves the record at `n = 8` (`102 → 282`, the best known value), `n = 9`
(`186 → 282`) and `n = 15` (`974 → 1406`, from `5·281·1²`).

**Witness.** `n₀ = 8`: `102 → 282`.

## V012 — `trial claude-fable` (based on V006, V010)

**Bound.** `record = maxWith V011.record (pin 3 (fun n => spencer n + 1))`, where `spencer n`
is the largest `N < 2^n` with
`2·(C(n,2)·(N−2)^(n−2) + (n−2)!)·2718281829 ≤ 2^C(n,2)·(n−2)!·10^9` — Spencer's exact
condition `e·p·(d+1) ≤ 1` with `C(N−2,n−2) ≤ (N−2)^(n−2)/(n−2)!` and `e < 2718281829/10^9`.

**Idea.** V010 used the local lemma in the `4pd ≤ 1` form. The exact `e·p·(d+1) ≤ 1` form
(Spencer 1975) is better by `(4/e)^(1/(n−2))`. The induction is V010's with the *product*
bound in place of the union bound: the dependent members of the conditioning family are
added one at a time (an inner `Finset.induction_on`), each keeping at least the fraction
`d/(d+1)` of the colourings by the outer induction hypothesis — the family is still
smaller than `Y` — so `|B_Y|·(d+1)^r ≥ d^r·|B_{Y₂}|` for `r ≤ d` dependent sets, and the
cleared condition `2·(d+1)^(d+1) ≤ 2^C·d^d` gives `|A_S ∩ B_Y|·(d+1) ≤ |B_Y|`. Positivity
needs only `d ≥ 1`, true for `N ≥ n` (`N < n` is trivial). The bridge from the record's
rational predicate to the cleared condition is `(1 + 1/d)^d ≤ exp 1` (`Real.add_one_le_exp`)
and Mathlib's `Real.exp_one_lt_d9`, the track's only real-number step. V010's events, fibre
count, independence and dependency count are reused unchanged.

**Why.** It improves the record at every `n ≥ 18`: `3333 → 3380` at `n = 18`,
`7569 → 7733` at `n = 20`, `401087 → 406659` at `n = 30`, `+0.8%` at `n = 50`, `+0.4%` at
`n = 100`. The lower record is now Spencer's theorem literally, up to the binomial-to-power
relaxation in the record's search.

**Witness.** `n₀ = 20`: `7569 → 7733`.

## V013 — `trial claude-fable` (based on V007, V012)

**Bound.** `record = maxWith V012.record (pin 3 (fun n => max (spencerE n) (altE n) + 1))`:
V012's Spencer search pushed upward while the *exact* condition
`2·(C(n,2)·C(N−2,n−2) + 1)·2718281829 ≤ 2^C(n,2)·10^9` holds, and V007's alteration bound
with the *exact* survivor count `N − ⌊2·C(N,n)/2^C(n,2)⌋`, maximised over a window above
V007's `N`.

**Idea.** No new mathematics: the power bounds `C(N,k) ≤ N^k/k!` that kept the records'
searches to one kernel power per probe are replaced by exact binomials, computed by the
recurrence `C(N,k+1) = C(N,k)·(N−k)/(k+1)` (structural in `k`; `Nat.choose_succ_right_eq`).
The scan keeps the exact condition invariant, so its result feeds `V012.not_forces`; the
exact alteration bound is V007's `exists_few` and `not_forces_alt` at `d = ⌊2·C(N,n)/2^C⌋`.
The kernel still evaluates the record at `n = 100` within budget; plain `decide` no longer
does (recursion depth), so `strict` — and later submitters — use `decide +kernel`.

**Why.** It improves the record at `n = 14` (`640 → 647`), `n = 17` (`2220 → 2228`) and at
every `n ≥ 18` by a few units (`7733 → 7742` at `20`, `406659 → 406672` at `30`). The two
probabilistic bounds are now the literal theorems, with no relaxation in the record.
5219 heartbeats in all.

**Witness.** `n₀ = 14`: `640 → 647`.

## Values

The **accepted record** at each version (each record is a `maxWith` of its predecessor, so
these are cumulative maxima), against the true value where known.

| n | V000 (seed) | V001 | V002 | V003 | V004 | V005 | V006 | V007 | V008 | V009 | V010 | V011 | V012 | V013 | true value / best known lower bound |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 |
| 3 | 5 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 |
| 4 | 10 | 10 | 10 | 18 | 18 | 18 | 18 | 18 | 18 | 18 | 18 | 18 | 18 | 18 | 18 |
| 5 | 17 | 26 | 26 | 26 | 26 | 38 | 38 | 38 | 38 | 43 | 43 | 43 | 43 | 43 | 43 ≤ · ≤ 46 |
| 6 | 26 | 26 | 26 | 26 | 26 | 38 | 38 | 38 | 102 | 102 | 102 | 102 | 102 | 102 | ≥ 102 |
| 7 | 37 | 37 | 46 | 69 | 86 | 86 | 86 | 86 | 102 | 102 | 102 | 102 | 102 | 102 | ≥ 205 |
| 8 | 50 | 50 | 50 | 69 | 86 | 86 | 86 | 86 | 102 | 102 | 102 | 282 | 282 | 282 | ≥ 282 |
| 9 | 65 | 126 | 126 | 126 | 126 | 149 | 149 | 149 | 186 | 186 | 186 | 282 | 282 | 282 | ≥ 565 |
| 10 | 82 | 126 | 126 | 290 | 290 | 290 | 290 | 290 | 290 | 290 | 290 | 290 | 290 | 290 | ≥ 798 |
| 11 | 101 | 126 | 126 | 290 | 290 | 290 | 290 | 290 | 506 | 506 | 506 | 506 | 506 | 506 | ≥ 1597 |
| 12 | 122 | 126 | 126 | 290 | 290 | 290 | 290 | 290 | 506 | 506 | 506 | 506 | 506 | 506 | ≥ 1637 |
| 13 | 145 | 145 | 226 | 290 | 426 | 426 | 426 | 426 | 630 | 630 | 630 | 630 | 630 | 630 | ≥ 2557 |
| 14 | 170 | 170 | 226 | 290 | 426 | 426 | 521 | 640 | 640 | 640 | 640 | 640 | 640 | 647 | ≥ 2989 |
| 15 | 197 | 197 | 246 | 290 | 426 | 426 | 786 | 974 | 974 | 974 | 974 | 1406 | 1406 | 1406 | ≥ 5485 |
| 16 | 226 | 226 | 246 | 426 | 426 | 426 | 1179 | 1474 | 1718 | 1718 | 1718 | 1718 | 1718 | 1718 | ≥ 5605 |
| 17 | 257 | 626 | 626 | 626 | 626 | 1370 | 1764 | 2220 | 2220 | 2220 | 2220 | 2220 | 2220 | 2228 | ≥ 8917 |
| 18 | 290 | 626 | 626 | 626 | 626 | 1370 | 2632 | 3333 | 3333 | 3333 | 3333 | 3333 | 3380 | 3388 | ≥ 11005 |
| 20 | 362 | 626 | 626 | 1157 | 1446 | 1446 | 5809 | 7438 | 7438 | 7438 | 7569 | 7569 | 7733 | 7742 | ≥ 24009 |
| 25 | 577 | 626 | 1126 | 1157 | 2126 | 2126 | 40546 | 52964 | 52964 | 52964 | 56753 | 56753 | 57714 | 57725 | unknown |
| 28 | 730 | 730 | 1126 | 4914 | 4914 | 4914 | 127691 | 168224 | 168224 | 168224 | 184478 | 184478 | 187239 | 187251 | unknown |
| 33 | 1025 | 3126 | 3126 | 4914 | 4914 | 5477 | 844719 | 1124876 | 1124876 | 1124876 | 1271439 | 1271439 | 1287382 | 1287397 | unknown |
| 49 | 2305 | 3126 | 5626 | 7226 | 10626 | 12322 | 316143815 | 429337043 | 429337043 | 429337043 | 514886614 | 514886614 | 519135920 | 519135943 | unknown |

V003 is exact at `n = 4` (`R(4,4) = 18`). Since V009, V008 and V011 the record also meets
the best known lower bound at `n = 5, 6, 8` (`43`, `102`, `282`). Each column is the accepted
record at that version (a cumulative maximum). The literature's values for `7 ≤ n ≤ 20`
are cyclic colourings found by computer (Exoo, Shearer, Mathon, Xu–Xie–Radziszowski, see
DS1) whose clique-freeness certificates are far beyond the computation budget; from
`n = 18` on the record is Spencer's local-lemma bound, the best known asymptotic bound.

## What the next improvement would take (as of V013)

Where the record stands: exact at `n ≤ 4`; equal to the best known lower bound at
`n = 5, 6, 8` (`43`, `102`, `282`); constructive lexicographic products of the five certified
bases (`C₅`, `Pal(17)`, `Pal(37)`, `Pal(101)`, `Pal(281)`) up to `n = 16`; the alteration
bound at `n = 14, 17`; and Spencer's local-lemma bound, with exact binomials, at every
`n ≥ 18`. The remaining gaps are `7 ≤ n ≤ 17`, where the literature's cyclic colourings are
two to four times larger, and the constant factors at large `n`.

- **Certified graphs are the bottleneck for `7 ≤ n ≤ 17`.** The tools now in the tree make a
  brute-force clique certificate affordable up to roughly a `K₆` check on 70 vertices
  (`V008.cliqueFree` with its soundness lemma; 29k heartbeats for `Pal(281)`'s common
  neighbourhood). With Euler's criterion as the residue test (V011) every Paley graph gets
  translation *and* multiplication symmetry for free, so `Pal(q)` with clique number `k`
  needs a `K_{k−2}` check on `(q−5)/4` vertices. Cheap remaining targets: `Pal(109)`
  (clique number 6; `K₅` on 26 vertices) gives `f 7 ≥ 110` against `102` — a one-value gain.
  `Pal(293)` (clique number 8) would give `f 9 ≥ 294` and `f 10 ≥ 294` but needs a `K₇` check
  on 73 vertices, about ten times the `Pal(281)` certificate, over the budget with the
  list-based checker; a bitset checker (candidate sets as naturals, one `Nat.land` per node,
  `Nat.log2` to pick the next vertex) would cut each node to a few accelerated operations
  and might fit, at the price of a soundness proof about bits of naturals. The literature's
  `(7,7,204)`, `(9,9,564)`, `(10,10,797)`, … graphs need `K₇`–`K₁₈` checks on hundreds of
  vertices and are out of reach.
- **Large `n`.** The record is Spencer's theorem literally; nothing better is known
  asymptotically (the only improvement since 1975 is off-diagonal, Ma–Shen 2025). The exact
  dependency count `Σ_{j≥2} C(n,j)·C(N−n, n−j)` in place of `C(n,2)·C(N−2,n−2)` would add
  about `+12` at `n = 20`: not worth a version on its own.
- **`R(5,5)` and `R(6,6)` are at the literature's values**, so the only way up at `n = 5, 6`
  would be a new mathematical result.

**Unfinished or parked work.** None in the record directories: V013 is the last version and
was accepted. Scratch files under `.lake/scratch/Ramsey-Lower/` (`Pal101Test.lean`,
`Pal281Test.lean`, `LLL.lean`, `Eform.lean`, `BinomTest.lean`, `DefTest*.lean`) hold the
experiments described above and the measured heartbeat costs; the downloaded graph6 file of
the 328 known `(5,5,42)`-graphs is `r55_42some.g6` there.

## What the next improvement would take (as of V005)

- **Mix `Pal(37)` in with the other two bases**, the way V004 mixed V002 and V003: the
  family is closed under lexicographic products, so `5^a·17^b·37^c·m²` vertices with
  clique and independence number `2^a·3^b·4^c·m` is available for every `a, b, c, m`.
  V005 only takes the pure `c` column and `maxWith`es it onto V004, so the genuinely mixed
  points (e.g. `n − 1 = 12 = 3·4`, where `17·37·1 = 629` beats both `37·9 = 333` and
  `17·16 = 272`) are still missing. All the pieces are in the tree: V005's `clique_card`
  and `lexAdj_dichotomy` are generic in the innermost relation, exactly as V003's were,
  so V004's plumbing carries over verbatim. This is the cheapest next version by a wide
  margin — no new graph has to be certified — and it improves the record at a positive
  fraction of all `n`.
- **A better base graph** would raise the exponent again: `log₄ 42 = 2.696` from the
  42-vertex circulant behind `R(5,5) ≥ 43`, or `log₅ 101 = 2.868` from `Pal(101)`
  (`R(6,6) > 101`). For `Pal(101)` the translation argument leaves a `K₄` check on the
  fifty residues, which is `50⁴` before short-circuiting — probably too much, so the
  multiplier symmetry (`x ↦ u·x` for `u` a residue, which fixes `0` and acts transitively
  on `N(0)`) would have to be formalised to cut it to a `K₃` check on `N(0) ∩ N(1)`.
  That is the natural next tool: it is what makes every Paley graph affordable.
- **Erdős' `2^(n/2)`** still beats every polynomial from about `n = 35` and remains the
  real prize; see the note below on what its formalisation needs.

## What the next improvement would take (as of V004)

- **A better base graph** is now the only way to raise the exponent: the family
  `{5^a·17^b·m²}` is closed under lexicographic products, so V004 is the best this pair of
  bases can give. `log₄ 42 = 2.696` from the 42-vertex circulant behind `R(5,5) ≥ 43` is
  the next step; certifying it is `K₅`-free needs the translation argument of V003 applied
  twice (a `K₅` through `0` is a `K₄` inside `N(0)`, 20 vertices, and that `K₄` has to be
  killed by a second symmetry — the circulant's multiplier group — or by a 20-vertex
  4-subset check, which is a search).
- **Erdős' `2^(n/2)`** still beats every polynomial from about `n = 35` and remains the
  real prize; see the note below on what its formalisation needs.

## Superseded note (written at V003)

- **Mix the two bases.** The construction family is closed under lexicographic products,
  so `5^a·17^b·m²` vertices with clique and independence number `2^a·3^b·m` is available
  for every `a, b, m`, i.e. `f n ≥ 5^a·17^b·m² + 1` whenever `2^a·3^b·m < n`. V003 only
  takes `a = 0`, V002 only `b = 0`; the maximum over all `(a, b, m)` is strictly larger at
  the `n` where neither pure split is optimal. All the pieces are in the tree already —
  V002's clique bound and dichotomy are generic in the innermost relation, so the V003
  power can be plugged into them as the innermost level.
- **A better base still.** `log₄ 42 = 2.696` from the 42-vertex circulant behind
  `R(5,5) ≥ 43`, or `log₄ 35` from `R(5,5) > 34` circulants; the `K₅`-free certificate
  would need the same translation trick one level deeper (a `K₅` through `0` becomes a
  `K₄` inside `N(0)`, which is again a 4-subset search unless the graph's automorphism
  group is used twice).

## What the next improvement would take (written at V002)

- **A better base graph.** This is now the only way up inside the construction family,
  since it is closed under products (see V002). Replacing `C₅` by the Paley graph on 13
  or 17 vertices (clique and independence number 3) would raise the exponent from
  `log₂ 5 = 2.322` to `log₃ 13 = 2.335` or `log₃ 17 = 2.579`; the 42-vertex graph behind
  `R(5,5) ≥ 43` would give `log₄ 42 = 2.696`. Two obstacles: the generic clique bound in
  V002 assumes a *triangle-free* base (it extracts three elements with
  `Finset.card_eq_three`), so it has to be restated for a `K₄`-free base; and certifying
  that the base has no `K₄` means checking all 715 (resp. 2380) four-subsets in the
  kernel. Heartbeat-wise that is affordable (V001's 125-case triple check costs ~825
  heartbeats, so ~5k resp. ~16k for both colours), but enumerating every subset is what
  the computation budget calls a search, so a reasoned proof of the Paley clique number
  would be needed instead. That is the honest reason this submitter stopped at V002.
- **The real prize** is Erdős' `2^(n/2)`, which beats any polynomial from about `n = 30`.
  The counting argument needs the cardinality of the set of graphs on `Fin N`
  (`2^C(N,2)`) and of those in which a fixed `n`-set is a clique; Mathlib has
  `SimpleGraph.card_topEdgeLabeling` but not the fibre count, so that bijection has to be
  built by hand.
