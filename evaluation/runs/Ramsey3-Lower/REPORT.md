# Ramsey3 — lower track report

`f(k) = R(3,k)`: the least `N` such that every 2-colouring of the edges of `K_N` has a triangle
in the first colour or a `K_k` in the second. `nMin = 2`.

A lower bound is a triangle-free graph: if `G` on `N` vertices is triangle-free and has
independence number `α(G) ≤ k-1`, then `N` does not force, so `R(3,k) ≥ N + 1`.

Accepted in this run, all by `baseline claude-opus-5`, starting from the seed
`V000 = 2k-1`:

| version | bound | linear constant | beats the previous at |
|---|---|---|---|
| V001 | `⌊5(k-1)/2⌋ + 1` | `5/2` | every `k ≥ 4` |
| V002 | `max(⌊5(k-1)/2⌋+1, 3k-4)` | `3` | every `k ≥ 6` |
| V003 | `max(V002, 13⌊(k-1)/4⌋+1)` | `13/4` | `k = 5`, every `k ≡ 1 (mod 4)` from `9`; all `k ≥ 32` |
| V004 | `max(V003, 13⌊(k-1)/4⌋ + 2((k-1) mod 4) + 1)` | `13/4` (better additive term) | every `k ≥ 10` with `k ≢ 1 (mod 4)` |

Accepted after that, by `trial claude-fable`:

| version | bound | growth | beats the previous at |
|---|---|---|---|
| V005 | `max(V004, g(k-1) + 1)`, `g m = max(base m, 6·g⌊m/4⌋)`, `base m = max(13⌊m/4⌋ + 2(m mod 4), ⌊5m/2⌋)` | `Ω(k^{log 6/log 4}) = Ω(k^{1.29})`, super-linear | `k = 9, 10, 13, 14` and every `k ≥ 17` |
| V006 | same recursion over `base m = 35⌊m/8⌋ + 13⌊(m mod 8)/4⌋ + [0,2,5,8][m mod 4]` | same exponent, constant `35/8` instead of `13/4` at the base | `k = 4, 7–16, 24–64, 97–100, …` (60 of the 99 values `k ≤ 100`; infinitely many) |
| V007 | `max(V006, q³ + 1)`, `q` the largest prime with `2q² ≤ k-1` | `Ω(k^{3/2})` | stretches from `k = 1683` on, every `k ≥ 8979` |

`V008` is the open Challenge.

## Literature

- Exact small values (Radziszowski, *Small Ramsey Numbers*, Electron. J. Combin. Dynamic
  Survey DS1; OEIS A000791): `R(3,2)=3`, `R(3,3)=6`, `R(3,4)=9`, `R(3,5)=14`, `R(3,6)=18`,
  `R(3,7)=23`, `R(3,8)=28`, `R(3,9)=36`; `40 ≤ R(3,10) ≤ 41`.
- Order of growth settled: `R(3,k) = Θ(k² / log k)` — upper bound Ajtai–Komlós–Szemerédi,
  *A note on Ramsey numbers*, JCTA 29 (1980); lower bound Kim, *The Ramsey number R(3,t) has
  order of magnitude t²/log t*, Random Structures Algorithms 7 (1995). The leading constant is
  open; current best constants come from the triangle-free process
  (Bohman–Keevash; Fiz Pontiveros–Griffiths–Morris, 2020): `R(3,k) ≥ (1/4 - o(1)) k²/log k`.
- Earlier explicit/probabilistic milestones: Erdős (1961) `R(3,k) > c (k/log k)²`;
  Spencer (1977) `R(3,k) ≥ c (k/log k)^{3/2}`.
- **Constructive (explicit) lower bounds**, which is what a Lean record can follow (added by
  `trial claude-fable`): Erdős, *On the construction of certain graphs*, J. Combin. Theory 1
  (1966) 149–153: `R(3,t) = Ω(t^{1.13})` (a Hamming-distance graph; the independence bound is
  Kleitman's diameter theorem). Cleve–Dagum (ICSI TR-89-009, 1989): `Ω(t^{1.26})`.
  Chung–Cleve–Dagum, *A note on constructive lower bounds for the Ramsey numbers R(3,t)*,
  J. Combin. Theory Ser. B 57 (1993) 150–155: `Ω(t^{log 6/log 4}) = Ω(t^{1.29})` by the
  *fibration* `G ↦ G × Z₆` used in V005. Alon, *Explicit Ramsey graphs and orthonormal
  labelings*, Electron. J. Combin. 1 (1994) R12: `Ω(t^{3/2})`, spectral (Lovász theta).
  Codenotti–Pudlák–Resta, Theoret. Comput. Sci. 235 (2000) 89–107, and Kostochka–Pudlák–Rödl,
  *Some constructive bounds on Ramsey numbers*, J. Combin. Theory Ser. B 100 (2010) 439–445:
  `Ω(t^{3/2})` from point–line incidence structures, with a *combinatorial* independence
  proof; Kocbek, arXiv:2507.09235 (2025) gives a self-contained version: order the points, take
  the flags `(p,ℓ)` as vertices, join `(p,ℓ)` to `(q,m)` when `ℓ ≠ m` and the smaller point lies
  on the other's line; then `α ≤ |P| + |L|`, and it is triangle-free when two points lie on at
  most one common line. Over `F_q` (affine, non-vertical lines) that is `q³` vertices and
  `α ≤ 2q²`. None of these is spectral or probabilistic; see *What next*.
- Maintainers' rule (2026-09-25): outside code only under Apache-2.0/MIT/BSD with attribution;
  mathematical data (a construction, a graph) with a citation; list every source under a
  *Sources* heading in the record's `REPORT.md`. V005 uses only the mathematical construction of
  Chung–Cleve–Dagum, cited there.
- All of these are genuine research formalisations. What is reachable here in a short session
  are **linear** bounds `R(3,k) ≥ c·k` with an explicit triangle-free witness family whose
  independence number is provable structurally (no subset search — the computation budget
  forbids it).

Blow-up principle used below: if `H` is triangle-free on `h` vertices with `α(H) = a`, then
replacing each vertex of `H` by an independent set of size `t` is triangle-free on `h·t`
vertices with independence number `a·t`, giving `R(3,k) ≥ (h/a)(k-1) + O(1)`. The best constant
obtainable from a fixed base `H` with `α(H) = a` is `(R(3,a+1)-1)/a`: `5/2` for `a = 2` (the
5-cycle), `13/4` for `a = 4`, `35/8` for `a = 8`. The obstacle is not the blow-up, it is proving
`α(H) ≤ a` for the larger bases without a search over subsets.

## Starting record

`V000` (SqueezeBench seed): `pin nMin (fun k => 2k - 1)`, from the complete bipartite graph
between evens and odds on `2k-2` vertices (ratio `2`).

## V001 — baseline claude-opus-5

**Bound:** `record k = ⌊5(k-1)/2⌋ + 1` for `k ≥ 2` (`pin`ned to `0` below `nMin = 2`).

**Idea.** The blow-up of the 5-cycle, laid out so that no re-indexing is needed: on `Fin N` the
vertex `x` carries the residue `x % 5`, and `x ~ y` iff the residues are consecutive mod `5`.
`C₅` is triangle-free, so the blow-up is; an independent set uses only residues that are
pairwise non-consecutive, and `C₅` has no independent set of three residues, so at most two
residue classes occur.

Taking `N = ⌊5(k-1)/2⌋` makes the two used classes hold at most `k-1` vertices *including* the
odd case. With `k-1 = 2q` all five classes have `q` elements. With `k-1 = 2q+1`, `N = 5q+2`, so
only the classes `0` and `1` have `q+1` elements — and those two are adjacent in `C₅`, hence
never both used. The formal proof avoids counting fibres: with `s` the smallest residue used,
`x ↦ 2·(x/5) + (0 if x % 5 = s else 1)` is injective on the independent set and lands in
`range (k-1)`; the case `x/5 = q` is exactly where the "classes `0` and `1` are adjacent"
argument is needed, and it is supplied by `s ≤ x % 5`.

This is the unbalanced-optimal blow-up: `⌊5(k-1)/2⌋` is the largest `C₅` blow-up with
independence number `≤ k-1`, since the five "diagonal" pairs of part sizes each sum to at most
`k-1` and together count every part twice.

**Why this one.** It dominates `V000` at *every* `k ≥ 2` (`⌊5m/2⌋ ≥ 2m` for all `m`), improves
it strictly at every `k ≥ 4`, and raises the linear constant from `2` to `5/2`. It also
reproduces two exact values: `record 2 = 3 = R(3,2)` and `record 3 = 6 = R(3,3)`, so together
with the upper seed `C(k+1,2)` the chain now machine-checks `R(3,3) = 6` as well as `R(3,2) = 3`.

**Witness.** `k = 9`: `V000` gives `17`, `V001` gives `21` (truth `36`).

**Cost.** 49796 heartbeats of the 200000 budget; the heaviest declaration is
`cadj_no_indep_three` (38259), an `omega` over three residues mod `5`.

## V002 — baseline claude-opus-5

**Bound:** `record = maxWith V001.record (pin nMin (fun k => 3k - 4))`, i.e.
`max(⌊5(k-1)/2⌋ + 1, 3k - 4)` for `k ≥ 2`; the second term wins at every `k ≥ 6`.

**Idea.** A circulant instead of a blow-up, which raises the constant from `5/2` to `3`. On
`Z_{3t+1}` join `x` and `y` when their cyclic distance is **more than** `t`.

- *Triangle-free.* For `a < b < c` pairwise joined, each of `b-a`, `c-b`, `c-a` lies strictly
  between `t` and `2t+1` (distance more than `t` in both directions round the circle). But
  `c - a = (b-a) + (c-b) > 2t`, contradicting `c - a < 2t+1`. One `omega` after unfolding the
  distance.
- *Independence number `t+1`.* An independent set `T` has all pairwise distances `≤ t`. Let `a`
  be its smallest element. Every `x ∈ T` then has `x - a ≤ t` or `x - a ≥ 2t+1`. The point of
  the modulus `3t+1` (rather than `3t`) is that these two kinds cannot be close: if `x - a ≤ t`
  and `y - a ≥ 2t+1` then `(y-a) - (x-a) ≥ t+1` *and* `3t+1 - ((y-a)-(x-a)) ≥ t+1`, so the
  distance constraint forces `(y-a) - (x-a) ≥ 2t+1`. Hence
  `x ↦ (x - a` if `x - a ≤ t`, else `x - a - 2t)` is injective on `T` and lands in `range (t+1)`.
  With `3t` instead of `3t+1` the "equilateral" set `{a, a+t, a+2t}` survives and the argument
  needs a case split; `3t+1` kills it and also gains a vertex.

Taking `t = k-2` gives a triangle-free graph on `3(k-2)+1 = 3k-5` vertices with independence
number `k-1`, so `R(3,k) ≥ 3k - 4`. The whole argument is ℕ arithmetic with `min`/`max` and no
`%`, so every step is one `omega`; nothing is searched.

**Why this one.** Ratio `3` beats ratio `5/2` at infinitely many `k` — at every `k ≥ 6`, and by
a margin growing like `k/2`. `V001` is still larger at `k = 2, 3` (where it is exact), so the
two are folded with `maxWith` rather than replaced.

**Witness.** `k = 9`: `V001` gives `21`, `V002` gives `23` (truth `36`).

**Cost.** 50159 heartbeats of the 200000 budget.

## V003 — baseline claude-opus-5

**Bound:** `record = maxWith V002.record (pin nMin (fun k => 13 * ((k-1)/4) + 1))`, i.e.
`max(V002, 13⌊(k-1)/4⌋ + 1)`. The new term wins whenever `13⌊(k-1)/4⌋ + 1 > 3k - 4`, which
holds at `k = 5`, at every `k ≡ 1 (mod 4)` from `k = 9` on, at every `k ≡ 2, 3` from `k = 22, 19`
on, and at every `k ≥ 32`. At `k = 5` it is exactly `R(3,5) = 14`: the base graph is the
extremal graph itself, so the new term is tight there.

**Idea.** The blow-up of `C₁₃(±1,±5)`, the extremal graph for `R(3,5) = 14`: on `Fin N` the
vertex `x` carries the residue `x % 13`, and `x ~ y` iff the residues differ by `±1` or `±5`
mod `13`. Its ratio `13/4` is the smallest ratio above `3` available at all: a triangle-free
graph with `n/α > 3` needs `α ≥ 4` (for `α = 2, 3` the maxima are `n = 5, 8`), and `α = 4`
forces `n ≤ 13` by `R(3,5) = 14`. So this is the unique next base graph.

- *Triangle-free.* Three differences from `{1,5,8,12}` never sum to `0` mod `13`; one `omega`
  over the 4·4·4 ways of choosing the three edge types (`radj_no_triangle`, 5189 heartbeats).
- *`α(C₁₃(±1,±5)) = 4`.* The cyclic-gap argument, which is the whole content of the version.
  Five residues in cyclic order have five gaps summing to `13`. A gap equal to `1` or `5` is an
  edge, so every gap is `≥ 2` and `≠ 5`, hence — the other four being `≥ 2` — every gap lies in
  `[2,4]`. Two consecutive gaps summing to `5` is again an edge (difference `5`, or `8 = 13-5`
  for the two pairs that wrap round), so no two consecutive gaps sum to `5`. The only gap
  multisets left are `(4,3,2,2,2)` and `(3,3,3,2,2)`; in the first the single `3` would need
  both its cyclic neighbours to be non-`2`, i.e. two distinct `4`s, and in the second each `2`
  would need both neighbours to be `2`, i.e. two other `2`s. `omega` does this last step from
  the five bounds and the five disequalities in one go (`gaps_absurd`).
- *Blow-up.* For `N ≤ 13q` the residues used by an independent set `T` form an independent set
  of `C₁₃(±1,±5)`, so at most `4` of them, and each residue class of `Fin N` has at most `q`
  members (`x ↦ x / 13` is injective on a class, into `range q`). Then
  `Finset.card_le_mul_card_image` gives `|T| ≤ 4q`.

Taking `q = ⌊(k-1)/4⌋` makes `4q ≤ k-1`, so `R(3,k) ≥ 13⌊(k-1)/4⌋ + 1`.

**Why this one.** It raises the linear constant from `3` to `13/4` and so beats V002 at
infinitely many `k` — at every `k ≥ 32`, and already at `k = 9, 13, 17, …`. V002 is larger at the
small `k` and at `k ≡ 0 (mod 4)` below `32`, so the two are folded with `maxWith`.

**Witness.** `k = 9`: V002 gives `23`, V003 gives `27` (truth `36`).

**Cost.** 170008 heartbeats of the 200000 budget — the tightest of the three versions. The
gap contradiction `no_indep_five` alone is 139651: it feeds `omega` ten non-edges, and `omega`
splits on the disequalities. Anything with more than five gaps will need the case analysis cut
down (see below).

## Getting there: two things worth knowing

- Extracting "five residues in increasing order" from a `Finset` is painless with
  `Finset.exists_subset_card_eq` followed by `Finset.orderIsoOfFin`: the order isomorphism
  `Fin 5 ≃o S` hands over the five elements *and* their order, `(g i : ℕ) < (g j : ℕ)` from
  `g.lt_iff_lt`, with no sorting boilerplate.
- Writing adjacency as `(x + 1) % 13 = y % 13 ∨ (x + 5) % 13 = y % 13 ∨ …` on plain naturals
  (rather than on `Fin 13`) keeps everything inside `omega`'s fragment, including the fact that
  adjacency only depends on the residues (`radj_mod`), and makes `SimpleGraph.fromRel` supply
  `symm` and `loopless`.

## V004 — baseline claude-opus-5

**Bound:** `record = maxWith V003.record (pin nMin (fun k => 13⌊(k-1)/4⌋ + 2((k-1) mod 4) + 1))`.
Writing `k - 1 = 4q + r` with `r < 4`, the new term is `13q + 2r + 1`; it beats V003's `13q + 1`
by `2r` whenever `r ≠ 0`, i.e. at every `k ≢ 1 (mod 4)`, and beats the folded record from
`k = 10` on (three quarters of all `k`, in particular infinitely many).

**Idea — the *unbalanced* blow-up.** V003 gave every residue class of `C₁₃(±1,±5)` the same size
`q = ⌊(k-1)/4⌋` and threw the remainder `r` away. Parts need not be equal: what must hold is
that every independent set of residues `I` satisfies `Σ_{ρ∈I} n_ρ ≤ k - 1`. Give the `2r`
residues `0, 1, …, 2r-1` one extra vertex each, so `N = 13q + 2r`. Then
`Σ_{ρ∈I} n_ρ = q|I| + |I ∩ [0,2r)| ≤ 4q + r = k - 1`, using two facts:

- `|I| ≤ 4` — V003's `indep_residues_card_le`, reused verbatim, the expensive cyclic-gap lemma;
- `|I ∩ [0,2r)| ≤ r` — **new, and cheap**: difference `1` is an edge of `C₁₃(±1,±5)`, so `I`
  contains no two consecutive residues, hence `ρ ↦ ρ/2` is injective on `I ∩ [0,2r)` and lands
  in `range r`. This is the one place the prefix shape matters, and it needs nothing about the
  connection set beyond `1 ∈ S`. (`prefix_indep_card_le`, a five-line injection.)

The report's earlier note predicted the extra classes would have to be chosen graph by graph
(`{0,1}` for `r = 1`, the eight non-neighbours of `0` for `r = 3`). The prefix `[0, 2r)` does it
uniformly for every `r` at once, because only the "no two consecutive" half of independence is
needed; `[0,2r)` induces a path, whose independence number is exactly `r`.

**Formalisation.** Triangle-freeness, `cg`, `cg_adj`, `radj_mod` and `indep_residues_card_le`
are imported from V003 unchanged. Only the count is redone: split the independent set `T` by
whether its residue lies in the prefix, `T = T₁ ∪ T₂`, with residue sets `I₁`, `I₂`. Fibres of
`T₁` have `≤ q+1` elements and fibres of `T₂` have `≤ q` (for `ρ ≥ 2r`, `x ≡ ρ` and
`x < 13q + 2r` force `x/13 < q`), so `Finset.card_le_mul_card_image` twice gives
`|T| ≤ (q+1)|I₁| + q|I₂| = q(|I₁|+|I₂|) + |I₁| ≤ 4q + r`. The two residue sets are disjoint and
their union is `T.image (· % 13)`, which is where `|I₁| + |I₂| ≤ 4` comes from.

**Why this one.** With ~10 minutes left, raising the ratio to `35/8` (`C₃₅(±1,±7,±11,±16)`) was
out of reach — the report's own analysis says the gap lemma there needs nine gaps and V003
already spends 140k of the 200k heartbeats on five. The unbalanced blow-up was the largest
available gain that reuses the expensive lemma untouched, and it improves at infinitely many `k`
rather than at a point.

**Witness.** `k = 10`: V003 gives `27`, V004 gives `29` (truth `40–41`). At `k = 20`:
`56 → 61`; at `k = 100`: `313 → 317`.

## V005 — trial claude-fable

**Bound:** `record = maxWith V004.record v`, `v k = g (k-1) + 1`, where
`base m = max (13⌊m/4⌋ + 2(m mod 4)) ⌊5m/2⌋` (the V004 and V001 graphs) and
`g m = max (base m) (6 · g ⌊m/4⌋)` (written with an explicit fuel `gAux` that stops below
`m = 4`, so the kernel unfolds it `⌊log₄ m⌋` times). Hence `g(4^r m₀) ≥ 6^r base m₀` and
`R(3,k) = Ω(k^{log 6/log 4})`: the first super-linear record on this track.

**Idea — the Chung–Cleve–Dagum fibration.** For a triangle-free `G` with independence number
at most `m`, `fib G` on `V(G) × Z₆` joins `(u,i)` to `(v,j)` when `u ~ v` and the layers `i, j`
are at cyclic distance at most `1`, and joins `(u,i)` to `(u,i+3)`.

- *Triangle-free.* A triangle of `G`-edges projects to a triangle of `G`. A matching edge
  `(u,i),(u,i+3)` has no common neighbour: a neighbour `(v,j)` with `v ≠ u` uses `G`-edges to
  both, so `j` is within `1` of both `i` and `i+3` — impossible mod `6`; with `v = u` it uses
  two matching edges, so `j = i+3 = i+6`. Eight cases, each one `omega` or a loop of `G`.
- *Independence ≤ 4m — the six-set lemma.* An independent `T ⊆ V × Z₆` has layers
  `A_i = {u : (u,i) ∈ T}` with `A_i ∪ A_{i+1}` independent in `G` (a `G`-edge between layers at
  distance `≤ 1` is an edge of `fib G`) and `A_i ∩ A_{i+3} = ∅` (a matching edge). Put
  `B_r = A_{2r} ∩ A_{2r+1}`. The `B_r` are pairwise disjoint (`B_0 ∩ B_1 ⊆ A_0 ∩ A_3` etc.) and
  `B_0 ∪ B_1 ∪ B_2` is independent (`B_0 ⊆ A_1`, `B_1 ⊆ A_2` and `A_1 ∪ A_2` is independent,
  and so on round the cycle). So `|T| = Σ|A_i| = Σ_r |A_{2r} ∪ A_{2r+1}| + Σ_r |B_r| ≤ 3m + m`.
  The independence half never uses that `G` is triangle-free.
- *Recursion.* `Good N m := ∃ G` on `Fin N`, triangle-free, every independent set `≤ m`.
  `good_c13`/`good_c5` come from V004's and V001's `indep_card_le` verbatim; `goodOn_comap`
  pulls `Good` back along any injection (`Fin.castLEEmb` for fewer vertices,
  `finProdFinEquiv` for `Fin N × Fin 6 ≃ Fin (N·6)`); `good_gAux` is an induction on the fuel.

**Why this one.** It changes the growth rate, not the constant: every fixed base graph blown
up is linear, this is `k^{1.29}`, and each later base-graph improvement at a small `m₀` now
propagates to all `k ≈ 4^r m₀`. It already beats V004 at `k = 9` (`31 > 27`, from
`6 · 5 = 30` vertices at `m = 8`) and at every `k ≥ 17`; at `k = 100` it gives `613` against
`319`, at `k = 1000` `9721` against `3244`.

**Witness.** `k = 17`: V004 gives `53`, V005 gives `79` (`6 · 13 = 78` vertices for `m = 16`).

**Cost.** 15466 heartbeats of the 200000 budget (`fib_cliqueFree` 6304, `six_set` 2643).
`squeeze verify` accepted; `decide +kernel` evaluates the recursion at every `n ≤ 100` easily.

**Provenance.** The construction is the paper's; the six-set lemma was reconstructed with a
literature consultation (GPT-6 Astra), then checked by hand and in Lean. No outside code.

## V006 — trial claude-fable

**Bound:** V005's recursion `g m = max (base m) (6 · g ⌊m/4⌋)` over the knapsack base
`base m = 35⌊m/8⌋ + rem (m mod 8)`, `rem r = 13⌊r/4⌋ + [0,2,5,8][r mod 4]`, i.e. the best
disjoint union of the certified pieces `(35,8)`, `(13,4)`, `(8,3)`, `(5,2)`, `(2,1)`.

**Idea.** Two new operations/pieces in the `Good N m` language of V005:

- *Disjoint union*: `Good N m → Good N' m' → Good (N+N') (m+m')` (`G ⊕g H`, `finSumFinEquiv`).
  With it the "optimal unbalanced blow-up" of `C₁₃` that the earlier notes wanted (`13q + 5` at
  `r = 2`, `13q + 8` at `r = 3`) comes for free: add a `C₅` or the Wagner graph `C₈(±1,4)`
  (`α = 3`, four gaps of size `≥ 2` summing to `8` — five disequalities and one `omega`).
- *The Kalbfleisch graph* `C₃₅(±1,±7,±11,±16)`, `α = 8`, extremal for `R(3,9) = 36`. The proof
  of `α ≤ 8` that fits the budget (111k heartbeats; the gap method was hopeless): in
  `Z₃₅ = Z₅ × Z₇` the graph is seven layers (`b + 7i`, each a 5-cycle with step `7`) with
  `(a,b) ~ (a+1, b+d)` for `d ∈ {1,2,4}` across layers. An independent set has `≤ 2` per layer,
  a full layer being `{x, x+21}`; with at most one full layer, `|I| ≤ 8`. With two, the
  automorphism `x ↦ q(x − x₁)` (`q ∈ {1,11,16}`, the units fixing the connection set) moves them
  to `{0,21}` and to layer `1`, where the second must be `{8,29}` or `{15,29}` (a `decide`
  table over `Fin 5 × Fin 5`). All other vertices non-adjacent to those four lie in a list of
  ten (resp. nine) candidates (`decide` over `Fin 35`), covered by two 5-cycles (resp. a 5-cycle
  and two edges): `|I| ≤ 4 + 2 + 2`. The 5-cycle bound is `fin5_no_consec`, a `decide` over
  the 32 subsets of `Fin 5`. Modular identities are `omega` with `q` split into its literals.

**Why this one.** The recursion multiplies whatever the base gives: raising the base ratio
from `13/4` to `35/8` (+35%) lifts `g` along every chain `m ∈ [8·4^r, 16·4^r)` and more, so the
record improves at 60 of the 99 values `k ≤ 100` and at infinitely many `k`, and it is now
exact at `k = 4` and `k = 9` (`R(3,4) = 9`, `R(3,9) = 36`), joining `k = 2, 3, 5`.

**Witness.** `k = 9`: V005 gives `31`, V006 gives `36`.

**Cost.** 125773 heartbeats of the 200000 budget; `two_doubles` 19.7k, `two_doubles'` 14.9k,
`kg_indep_card_le` 14.1k. (A first Wagner lemma that gave `omega` the raw `% 8` hypotheses
cost 88k on its own; deriving five plain disequalities first made it 3k. `decide` over the
256 subsets of `Fin 8` hits the elaborator's recursion limit — keep such tables at `Fin 5`
size, or over `Fin n` elements rather than `Finset (Fin n)`.)

**Provenance.** The graph is Kalbfleisch's (1966), via Radziszowski's survey; the proof of
`α ≤ 8` was obtained with a consultation (GPT-6 Astra), checked by hand and against a
computer enumeration of all 3360 maximum independent sets before formalising. No outside code.

## V007 — trial claude-fable

**Bound:** `record = maxWith V006.record v`, `v k = inc (k-1) + 1`, `inc m = q³` for the largest
prime `q` with `2q² ≤ m` (`isqrt` by linear search, `primeBelow` by downward search, `isPrime`
by trial division — all structurally recursive, so `decide +kernel` evaluates them; at the
witness the kernel does about 60 small steps).

**Idea — the ordered incidence graph** (Codenotti–Pudlák–Resta 2000, Kostochka–Pudlák–Rödl
2010, in Kocbek's form, arXiv:2507.09235 Def. 2.2, Thms 2.3–2.4). For a prime `p`, flags
`(x, s, b) ∈ (Z/p)³` = the point `(x, sx+b)` on the line `y = sx + b`; points ordered by the code
`x·p + y ∈ ℕ`; `f ~ g` iff their lines differ and the smaller point lies on the other's line.
Triangle-free: a triangle has points `f < g < h`, and the points of `f, g` lie on the distinct
lines of `g` and `h` — impossible, two distinct points determine at most one non-vertical
line (`(s−s')(x−x') = 0` in a field). Independence `≤ |P| + |L| = 2p²`: the flags whose point is
the largest of the set on their line are at most one per line; every other flag `(p,ℓ)` has a
larger `(q,ℓ)` in the set, so a second flag `(p,ℓ')` at the same point would be adjacent to
`(q,ℓ)` — at most one per point. `Good (p³) (2p²)`, transported to `Fin (p³)` by
`Fintype.equivFinOfCardEq`. Lean: `two_points` (`linear_combination`, `mul_eq_zero`),
`no_triangle` (8 orientations, 2 cyclic by `omega`), `ig_indep_card_le` (two injections into
`univ : Finset (ZMod p × ZMod p)`), `isPrime_prime` (`Nat.prime_def_lt`) to make `ZMod q` a
field. 29574 heartbeats in all.

**Why this one.** It is the best *exponent* an elementary proof gives (`3/2`, Alon's explicit
bound, without spectral methods). Its constant is poor (`α ≤ 2p²` on `p³` vertices), so it
only overtakes V006's `35/8 · 1.5^r` chain from `k = 1683` (`q = 29`) on: on the stretches
`[1683,1728]`, `[1923,2048]`, `[3363,4096]`, `[4419,5120]`, `[5619,8192]` and at every
`k ≥ 8979` (Python scan to `2·10⁵`). Nothing changes at `k ≤ 100`. Prime powers
(`GaloisField`) would add `q = 27, 32, 49, 64, …` and start at `k = 1459`.

**Witness.** `k = 1683`: V006 gives `23761`, V007 gives `24390`.

## Values

(V004's row is recomputed here; the earlier table had `14, 61, 317` at `k = 6, 20, 100`, which
were typos — `13·1+2·1+1 = 16`, `13·4+2·3+1 = 59`, `13·24+2·3+1 = 319`.)

| k | 2 | 3 | 4 | 5 | 6 | 9 | 10 | 13 | 17 | 20 | 33 | 65 | 100 | 1000 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| V000 `2k-1` | 3 | 5 | 7 | 9 | 11 | 17 | 19 | 25 | 33 | 39 | 65 | 129 | 199 | 1999 |
| V001 `⌊5(k-1)/2⌋+1` | 3 | 6 | 8 | 11 | 13 | 21 | 23 | 31 | 41 | 48 | 81 | 161 | 248 | 2498 |
| V002 `max(V001, 3k-4)` | 3 | 6 | 8 | 11 | 14 | 23 | 26 | 35 | 47 | 56 | 95 | 191 | 296 | 2996 |
| V003 `max(V002, 13⌊(k-1)/4⌋+1)` | 3 | 6 | 8 | 14 | 14 | 27 | 27 | 40 | 53 | 56 | 105 | 209 | 313 | 3237 |
| V004 `max(V003, 13q+2r+1)` | 3 | 6 | 8 | 14 | 16 | 27 | 29 | 40 | 53 | 59 | 105 | 209 | 319 | 3244 |
| V005 `max(V004, g(k-1)+1)` | 3 | 6 | 8 | 14 | 16 | 31 | 31 | 43 | 79 | 79 | 181 | 469 | 613 | 9721 |
| **V006 (base with `C₃₅`)** | **3** | **6** | **9** | **14** | **16** | **36** | **38** | **49** | **79** | **79** | **211** | **469** | **649** | **12097** |
| V007 (`+ q³ + 1`) | same as V006 at every `k ≤ 1682`; `k = 1683`: `24390` (V006 `23761`), `k = 10⁴`: `148878` (`134137`), `k = 10⁵`: `11089568` (`2099521`) |||||||||||||||
| true `R(3,k)` | 3 | 6 | 9 | 14 | 18 | 36 | 40–41 | ≥ 60 | ≥ 92 | ≥ 111 | ? | ? | ? | ? |

## What the next improvement would take

**The ceiling of the method.** A fixed base graph `H` blown up gives the linear bound
`(n(H)/α(H))·(k-1) + O(1)`, and nothing better. Anything super-linear (`Ω(k^{3/2})` by
Spencer's deletion argument, `Ω(k²/log k)` by Kim / the triangle-free process) is a research
formalisation, far outside a session of this length. So the next versions are about the base.

**The base graphs available.** An exhaustive search over triangle-free *circulants* `C_n(S)`
for `n ≤ 37` (connection sets up to 5 generator pairs; script logic: `S` symmetric, triangle-free
iff `(S+S) ∩ S = ∅`, `α` by branch and bound) gives the best ratio `n/α` at each `n`:

| n | 13 | 20 | 21 | 24 | 26 | 29 | 30 | 31 | 32 | 33 | 35 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| connection set `±S` | `1,5` | `1,5,8` | `1,3,8` | `1,6,10` | `1,3,8,13` | `1,5,13` | `1,3,7,12` | `1,3,5,12` | `1,4,6,15` | `1,6,10,15` | `1,7,11,16` |
| `α` | 4 | 6 | 6 | 7 | 7 | 8 | 8 | 8 | 8 | 8 | 8 |
| ratio | 3.25 | 3.33 | 3.50 | 3.43 | 3.71 | 3.63 | 3.75 | 3.88 | 4.00 | 4.13 | **4.375** |

`C₃₅(±1,±7,±11,±16)` with `α = 8` is the extremal graph for `R(3,9) = 36` and is the target
worth aiming at: ratio `35/8 = 4.375` against the `13/4` of V003. `C₂₁(±1,±3,±8)`, ratio `3.5`,
is the cheap intermediate step.

**The obstacle is the independence number, and it is a budget problem.** The blow-up half of
V003 (`indep_card_le`, `cg_cliqueFree_three`, the fibre count) is generic: only the modulus
`13`, the connection set and the number `4` appear in it, so it transplants to any circulant in
an hour. What does not transplant is `no_indep_five`, and V003 already spends
**139651 of the 200000 heartbeats** on it. The cyclic-gap scheme scales badly: for `C₂₁` one
must refute seven gaps summing to `21`, for `C₃₅` nine gaps summing to `35`, and `omega` splits
on every disequality it is handed. Two ways out, both untried here:

1. *Feed `omega` less.* Derive the gap bounds (`2 ≤ gᵢ ≤ 4` in V003) in small separate lemmas
   with clean contexts, and let the final lemma see only the gap variables — never the ten
   non-edge hypotheses. In V003 the ten `not_radj_diff` facts all sit in the context when the
   eleven `by omega` side goals are elaborated, and that is where the 139k goes.
2. *Split by hand.* Case on the multiset of gaps rather than letting `omega` find it: with
   minimum gap `2` and sum `n`, the multiset is one of a handful, and each is killed by a
   one-line adjacency of two consecutive gaps.

**Cheap constant gains — V004 took the uniform one; what is left.** The prefix trick of V004
gives `2r` extra vertices. The *optimal* unbalanced blow-up gives more: the extra classes only
have to induce a subgraph of independence number `≤ r`, and for `r = 3` the largest such set has
`8` residues, not `6`, so `N = 13q + 8` rather than `13q + 6`. The gain is `+2` at `k ≡ 0 (mod 4)`
only, and it costs a bespoke `α ≤ 3` proof for an 8-vertex induced subgraph, so it is not worth a
version on its own. The original note is kept below.

**Cheap constant gains, if a version is wanted quickly.** The blow-up is balanced, so it wastes
the remainder `r = (k-1) mod 4`. Parts may be unbalanced: giving `+1` vertex to each class of a
set `E ⊆ Z₁₃` is legitimate as soon as `α(C₁₃[E]) ≤ r`, so `N = 13q + 2` for `r ≥ 1` (`E` an
edge, e.g. `{0,1}`), `N = 13q + 8` for `r = 3` (`E` the eight non-neighbours of `0`, whose
induced independence number is `3`). The same effect is reached with no new base-graph work by
taking the **disjoint union** with the C₅ blow-up of V001: a graph on `⌊5r/2⌋` vertices with
independence number `r`, giving `N = 13⌊(k-1)/4⌋ + ⌊5r/2⌋`. Either way the gain is at most `+8`,
constant in `k` — worth doing only after the ratio has been pushed.

For the count to come out, `Finset.card_le_mul_card_image` has to be replaced by
`Finset.card_eq_sum_card_fiberwise` plus a per-class bound, since the classes then have two
different sizes.

## Notes added after V004 (no new version: the session ended)

Two concrete facts checked by hand while looking for a `V005`, both aimed at the unbalanced
blow-up of `C₁₃(±1,±5)`:

- *The prefix `[0,2r)` of V004 is not optimal at `r = 2`.* The five residues `{0,1,2,3,8}`
  induce a **C₅** in `C₁₃(±1,±5)` — the cycle `0–1–2–3–8–0` uses differences `1,1,1,5,8`, and
  the five remaining pairs (`0-2`, `0-3`, `1-3`, `1-8`, `2-8`, differences `2,3,2,7,6`) are all
  non-edges. So `α = 2` on a set of size `5`, against the `4` of the prefix `[0,4)`: taking
  `E = {0,1,2,3,8}` when `r = 2` gives `N = 13q + 5`, one more than V004. At `r = 3` the report's
  eight-vertex set gives `13q + 8`, two more. At `r = 1` the prefix is already optimal (a set with
  `α = 1` is a clique, and the graph is triangle-free, so `|E| ≤ 2`). Total available gain over
  V004: `+1` at `k ≡ 3 (mod 4)` and `+2` at `k ≡ 0 (mod 4)`, i.e. constant in `k` — worth folding
  in only alongside a ratio improvement, and it costs one bespoke `α ≤ r` lemma per residue `r`,
  since the three sets have no common shape.
- *Widening the prefix to `[0, 2r+1)` does not work*, which is worth knowing because it looks
  free. The set `{0,2,4,6}` is independent in `C₁₃(±1,±5)` (differences `2,4,6`, none in
  `{1,5,8,12}`), it has size `4` — the maximum — **and** it already meets `[0,2r+1)` in `r+1`
  classes at `r = 1` and at `r = 3`. So the "an independent set of size `4` meets the prefix in
  at most `r` classes" step, which is the whole of V004's count, fails at the first residue one
  would try. Any wider extra set has to be chosen so that the size-`4` independent sets meet it
  in `≤ r` classes, and `{0,2,4,6}` is the binding constraint.

The ratio is still the thing to attack: `C₂₁(±1,±3,±8)` (`α = 6`, ratio `3.5`) then
`C₃₅(±1,±7,±11,±16)` (`α = 8`, ratio `4.375`), with the heartbeat problem of `no_indep_five`
addressed by the two routes listed above.

**Problems hit.** None serious. Besides the two notes above: `SimpleGraph.fromRel` is the
painless way to get `symm`/`loopless` for a relation defined through `%`; `split_ifs` rather
than `simp only [h, if_pos]` is what keeps `omega` able to see that an `if`-term is `0` or `1`;
and cyclic distance with a *variable* modulus must be written with `min`/`max` and truncated
subtraction, not `%`, because `omega` cannot reason about `% n` for a variable `n` (V002). With
a *literal* modulus, as in V003, `%` is fine and `omega` handles even nested `(x % 13 + 1) % 13`.

## Notes by trial claude-fable: where the next improvements are

The record is now `g(k-1) + 1` with `g m = max (base m) (6·g⌊m/4⌋)`; every improvement of
`base` at some `m₀` lifts all `k ≈ 4^r m₀`, and every better recursion lifts everything.

1. **More base pieces.** The remaining extremal graphs: `(17,5)`, `(22,6)`, `(27,7)` (the
   `R(3,6..8)` graphs; none is a circulant — the circulant search gives `α = 6, 7, 8` at
   `n = 17, 22, 27`), `(39,9)` (`R(3,10) ≥ 40`, not a circulant either), and the cyclic graphs
   behind the known lower bounds for `R(3,k)`, `k ≥ 11` (Radziszowski DS1, Exoo). A piece
   `(n, a)` is worth having iff `n/a > 35/8 = 4.375` or it improves a remainder `r < 8`:
   `(17,5)` beats `rem 5 = 15`, `(22,6)` beats `rem 6 = 18`, `(27,7)` beats `rem 7 = 21`, and
   `(39,9)`, `(46,10)`, … have ratios `4.33, 4.6, …`. Each needs its own `α` proof; the pattern
   of V006 (layers, automorphisms, `decide` tables over `Fin n`, cycle covers) is the template,
   and a covering by odd cycles/edges only works when the fractional odd-cycle bound is tight,
   which one should check by computer first (it fails for the Wagner graph, for instance).
   Cheap intermediate: `C₂₁(±1,±3,±8)`, `α = 6`, ratio `3.5` — it beats `rem 6 = 18` by `3`.
2. **A better recursion.** The layered schemes `V × Z_m` with `G`-edges between layers at
   distance in `D` and matchings between layers at distance in `M` were explored by an LP
   (script `lp_schemes.py` in the scratch directory, z3 as LP solver): for `m = 6, 7` the
   Chung–Cleve–Dagum scheme (`m = 6`, `D = {0,±1}`, `M = {3}`, factor `4`) is optimal; the
   exponent `log 6/log 4` is tight for that scheme (the fibration of a graph with two disjoint
   maximum independent sets again has two). Anything better must be a different kind of
   product.
3. **The exponent 3/2.** The ordered point–line incidence graph (Codenotti–Pudlák–Resta;
   Kostochka–Pudlák–Rödl; Kocbek arXiv:2507.09235) is elementary: flags `(p,ℓ)`, `(p,ℓ) ~ (q,m)`
   iff `ℓ ≠ m` and the smaller point lies on the other's line; triangle-free when two points
   determine at most one line; `α ≤ |P| + |L|` by a two-line injection argument. Over `F_q`
   (affine plane, non-vertical lines) it is `q³` vertices with `α ≤ 2q²`. Its constants are
   poor: it beats V006 only from `k ≈ 1500` on (`q = 27`), and first for a prime at `q = 29`
   (`k = 1683`). Still infinitely many `k` and a better exponent; the record function would
   take the largest prime power `q` with `2q² ≤ k-1`, and the Lean side needs `ZMod p` (or
   `GaloisField`), an injection `Fin (q³) ≃ F³`, and the two lemmas above. Worth a version once
   the base is exhausted.
4. **Disjoint union inside the recursion.** `g` could also use `g (m₁ + m₂) ≥ g m₁ + g m₂`
   (e.g. `g 20 ≥ g 16 + g 4 = 78 + 13 = 91` vs `90` now). Gains are small and sporadic; a
   knapsack over `{fibration outputs}` is cheap to evaluate but needs a careful fuel argument.

## State at the end of the session (trial claude-fable)

Accepted: V005 (fibration recursion), V006 (base with `C₃₅`, disjoint unions, Wagner graph),
V007 (incidence graph, exponent `3/2`). Nothing is parked half-done inside a version
directory; the unfinished threads are explorations, all in the session's scratch directory
under `.lake/scratch/Ramsey3-Lower/` (`scratchpad/`):

- `lp_schemes.py` (needs the `z3` binary): the LP over layered schemes `V × Z_m`; `lp_out.txt`
  has the results for `m = 6, 7` and part of `m = 8` — nothing beats the Chung–Cleve–Dagum
  factor `6/4`. It is slow (constraint generation with one z3 call per iteration); a real LP
  solver would finish `m ≤ 12` in minutes.
- `circ.py`, `circ2.py`, outputs `circ2_out.txt`, `circ3_out.txt`: the best triangle-free
  circulants `C_n(S)` and their independence numbers, complete for `n ≤ 66`. Beyond `C₃₅` the
  ratios keep rising: `C₄₄(±7,±15,±16,±18,±20)` `α = 10` (4.40), `C₄₅(±6,±13,±20,±21,±22)` `α = 10`
  (4.50), `C₅₄(±12,±17,±19,±22,±26,±27)` `α = 12` (4.50), `C₅₅(±12,±18,±21,±23,±26,±27)` `α = 12`
  (4.58), `C₅₆(±9,±19,±20,±22,±24,±26)` `α = 12` (4.67), `C₅₇(±12,±16,±20,±22,±26,±27)` `α = 12`
  (4.75), `C₆₃(±10,±11,±24,±27,±30,±31)` `α = 13` (4.85), `C₆₆(±12,±18,±28,±29,±31,±32,±33)`
  `α = 14` (4.71). **This is the next base improvement**: a piece `(57,12)` or `(63,13)` in the
  knapsack raises the constant of the whole recursion by 9–11% and lifts about half of the
  values `k ≤ 100`. Each needs an `α` proof in the style of V006 (`Z_n ≅ Z_a × Z_b` layers,
  automorphism normalisation, `decide` tables over `Fin n`, covers by odd cycles and edges);
  check by computer first that a cycle cover exists in the normalised configurations. The
  generator in `circ2.py` (backtracking over symmetric sum-free sets) handles `n ≈ 90` in
  minutes if one wants to look further.
- `c35.py`, `c35b.py`, `modelB.py`: the enumeration of the 3360 maximum independent sets of
  `C₃₅` and their layer structure, used to check the V006 proof before formalising.
- `gains.py`, `wins7.py`, `incid.py`: the record models used for the tables above.
- `k35b.lean`, `v6a.lean`, `inc1.lean`, `inc2.lean`: the scratch versions of the V006 and V007
  proofs (superseded by the accepted files).

What a next session should do, in order of value: (1) certify `C₅₇` or `C₆₃` (and `C₂₁`,
`C₂₆` for the remainders `6, 7`) and add them to `base`; (2) prime powers in V007 via
`GaloisField`; (3) a disjoint-union step inside the recursion (`g (m₁+m₂) ≥ g m₁ + g m₂`).
