# ExGirthFive — upper track report

`f(n) = ex(n; {C₃, C₄})`, the largest number of edges of a graph on `n` vertices of girth at
least `5`. `nMin = 1`. Starting record (seed `V000`): `C(n, 2)`.

## Literature

- **Moore-type bound.** For a graph of girth ≥ 5 on `n` vertices with `m` edges,
  `m ≤ ½·n·√(n−1)`, i.e. `≈ 0.5·n^{3/2}`. It comes from the neighbourhood count
  `1 + Σ_{u ~ v} d(u) ≤ n` for each vertex `v`, equivalently `Σ_v d(v)² ≤ n² − n`, plus
  Cauchy–Schwarz. Standard; stated e.g. in Garnick–Kwong–Lazebnik, *Extremal graphs without
  three-cycles or four-cycles*, J. Graph Theory **17** (1993) 633–645, and in the problem
  README. Equality holds exactly for Moore graphs of diameter 2 — the 5-cycle (`n = 5`), the
  Petersen graph (`n = 10`), the Hoffman–Singleton graph (`n = 50`), and possibly a
  (57, 2)-Moore graph (`n = 3250`, existence open).
- **Leading constant.** Garnick–Kwong–Lazebnik:
  `1/(2√2) ≤ limsup ex(n;{C₃,C₄})/n^{3/2} ≤ 1/2`. The lower end is the incidence graph of a
  projective plane; Erdős conjectured it is the truth
  ([Erdős problem #573](https://www.erdosproblems.com/573)). Improving the constant `½` in the
  upper bound is therefore open, so on this track everything beyond `½·n·√(n−1)` is
  lower-order.
- **Lower-order improvements.** The known refinements are degree-sequence / integrality
  arguments and a recursion `f(n) ≤ f(n−1) + δ` on the minimum degree; see Abajo–Diánez et al.,
  *Some new upper bounds of `ex(n;{C₃,C₄})`*, AKCE Int. J. Graphs Comb. (2017), and
  Garnick–Kwong–Lazebnik 1993. Exact values are known for `n ≤ 53` (OEIS A006856); they are
  *reporting only* here and may not be used as theorems.
- **Lower side, for context.** Ma–Yang (2025),
  [arXiv:2508.05562](https://arxiv.org/pdf/2508.05562), improved the lower bound by an additive
  `c·n^{5/4}` — the first gain since 1976 — without moving the constant.

## V001 — baseline claude-opus-5

Bound: `record n = min( C(n,2), ⌊√(n²(n−1))⌋ / 2 )`, written in ℕ as
`Nat.sqrt (n * (n * n − n)) / 2` — the Moore bound `½·n·√(n−1)`. This drops the record from
order `n²` to order `n^{3/2}`, the best order known.

Proof idea, all inside `Proof.lean`:

1. *Cherries.* A **cherry** is a centre `w` with an ordered pair of distinct neighbours
   `(x, y)`; they form `cherries G`, of size `Σ_w (d(w)² − d(w))`. The map `(w,x,y) ↦ (x,y)`
   lands in the ordered **non-adjacent** pairs (`x ~ y` would make `{w,x,y}` a triangle) and is
   injective (two centres for the same `(x,y)` is exactly the forbidden pair of distinct
   vertices with two distinct common neighbours — the `NoTwoCommonNeighbours` half of
   `five_le_egirth_iff`).
2. *Arcs.* The ordered adjacent pairs, of size `Σ_w d(w)`, inject into the ordered adjacent
   pairs. Since "adjacent" and "non-adjacent" split `univ.offDiag`, the two counts add:
   `Σ_w (d(w)² − d(w)) + Σ_w d(w) ≤ n² − n`, i.e. **`Σ_w d(w)² ≤ n² − n`**.
3. *Cauchy–Schwarz* (`sq_sum_le_card_mul_sum_sq`, which applies over ℕ):
   `(2m)² = (Σ_w d(w))² ≤ n·Σ_w d(w)² ≤ n(n² − n)`, so `2m ≤ ⌊√(n²(n−1))⌋` and
   `m ≤ ⌊√(n²(n−1))⌋ / 2`.

Chosen because it is the whole of the classical theory in one step and is *tight* for every
`n ≤ 10` (it gives the true `f(n)` there, the Petersen graph at `n = 10` included). Folded in
with `minWith` (Idiom 2) rather than proved to dominate `C(n,2)` pointwise.

Witness `n₀ = 10`: `C(10,2) = 45` → `15`, the exact value `f(10) = 15`.

Note for later submitters: `Nat.sqrt` is defined by well-founded recursion, so plain `decide`
gets stuck on the record; `decide +kernel` (what the fuel gate itself uses) evaluates it fine
and cheaply.

## V002 — baseline claude-opus-5

Bound: `record n = min( V001.record n, min_{q ∈ {s−1, s, s+1}} ⌊ n(n−1+q²+q) / (2(2q+1)) ⌋ )`
with `s = ⌊√(n−1)⌋`.

Same degree inequality `Σ_w d(w)² ≤ n² − n`, but with Cauchy–Schwarz replaced by the
**integrality (tangent-line) bound**: for all naturals `d, q`,
`(2q+1)·d ≤ d² + q(q+1)` — the chord of `x ↦ x²` through `(q,q²)` and `(q+1,(q+1)²)`. Summing,
`(2q+1)·2m ≤ Σ_w d(w)² + n·q(q+1) ≤ n(n − 1 + q² + q)`, hence
`m ≤ ⌊ n(n−1+q²+q) / (2(2q+1)) ⌋` for **every** `q`. Taking the best `q` recovers Cauchy–Schwarz
in the real relaxation, but the two floors (in `q` and in the quotient) gain whenever the
optimal real degree `2m/n` is far from an integer. Only the three `q` nearest `√(n−1)` are
needed: over `1 ≤ n ≤ 400`, `q ∈ {s−1, s, s+1}` already attains the minimum over all `q`, so the
record stays `O(1)` to evaluate.

This improves V001 at **224 of the first 400 values of `n`** (first at `n = 15`, then
`32, 35, 43, 44, 45, 46, 53, 55, 57, 61, 62, …`), by `1` and occasionally `2`. Chosen over a
one-point patch for exactly that reason.

The degree-sequence relaxation is exhausted by this: the best integer degree sequence with
`Σ d(w)² ≤ n² − n` has `n − r` vertices of degree `s` and `r` of degree `s+1` with
`r = ⌊n(n−1−s²)/(2s+1)⌋`, and `(ns + r)/2` is exactly `bnd n s`. So no further gain is available
from `Σ d(w)² ≤ n² − n` alone.

Witness `n₀ = 15`: `28` → `27` (true value `f(15) = 26`).

## V003 — baseline claude-opus-5

Bound: `record n = min( V002.record n, min_{q ∈ {s−1, s, s+1}} bnd(n, q) )` with `s = ⌊√(n−1)⌋`,
where, writing `L = min( ⌊(n−1)/(q+1)⌋ , q )`,

```
bnd(n, q) = max( ⌊ n·q / 2 ⌋ ,
                 ⌊ ( L·(2q+1−L) + n(n−1) + (n−1)·q(q+1) ) / (2(2q+1)) ⌋ )
```

The new ingredient is the **per-vertex** form of the degree count, which V001/V002 only ever used
after summing. For every vertex `x`, the vertices at distance exactly `2` from `x` are pairwise
distinct (two of them would give `x` and that vertex two common neighbours) and avoid `N[x]`
(a common neighbour of `x` and of a neighbour of `x` would close a triangle), so

> **`Σ_{u ∼ x} d(u) ≤ n − 1`  (`nbr_sum_le` in `Proof.lean`).**

Summing this over `x` is exactly `Σ_w d(w)² ≤ n² − n`; keeping it per vertex gives more. Fix `q`
and split:

* if every degree is at most `q`, then `2m = Σ d(w) ≤ n·q`, the first branch of the `max`;
* otherwise some vertex `v` has `d(v) ≥ q+1`. Its `d(v)` neighbours all have degree at least the
  minimum degree `δ`, so `(q+1)·δ ≤ d(v)·δ ≤ Σ_{u ∼ v} d(u) ≤ n − 1`, i.e. `δ ≤ ⌊(n−1)/(q+1)⌋`.
  Now pull a vertex `w` of degree `δ` **out** of the chord sum: applying the V002 chord only to
  the other `n − 1` vertices gives
  `(2q+1)(2m − δ) ≤ (Σ d² − δ²) + (n−1)q(q+1)`, hence
  `(2q+1)·2m ≤ [(2q+1)δ − δ²] + n(n−1) + (n−1)q(q+1)`.
  The bracket is `≤ L(2q+1−L)` (`chord2`), because `x ↦ (2q+1)x − x²` increases up to `q` and
  `δ ≤ L`. Against V002's `n·q(q+1)` this is smaller by `q(q+1) − L(2q+1−L)`, which is `2` when
  `L = q − 1` (and `0` when `L = q`, so the bound never loses).

So the gain is exactly the case where the minimum degree is forced strictly below `q`: it happens
when `n − 1 < q(q+1)`, i.e. roughly half of all `n`, but it is worth only `2` in `2m` and
therefore survives the floor at **12 of the first 400 values of `n`**:
`18, 39, 68, 105, 108, 150, 155, 203, 264, 333, 375, 377`, each by `1`. Chosen because it is the
first genuinely new *combinatorial* input on this track since V001 and it keeps improving as `n`
grows; the `nbr_sum_le` lemma it introduces is also the entry point for the stronger bounds
described at the end of this report.

Witness `n₀ = 18`: `37` → `36` (true value `f(18) = 34`).

## V004 — baseline claude-opus-5

Bound: `record n = min( V003.record n, min_{q ∈ {s−1, s, s+1}} bnd(n, q) )` with `s = ⌊√(n−1)⌋`,
where

```
bnd(n, q) = max( ⌊ n·q / 2 ⌋ ,
                 ⌊ ( n(n−1) + n·q(q+1) + 2(n−1) − 2·q(q+1) ) / (2(2q+1)) ⌋ )
```

The same per-vertex count `∑_{u ∼ x} d(u) ≤ n − 1` as V003, but now the *whole neighbourhood* of
a high-degree vertex is exploited instead of only its consequence on the minimum degree.

Write the chord of `x ↦ x²` at `q` with its slack explicit: for every `d`,
`(2q+1)d + 2q ≤ d² + q(q+1) + 2d`, i.e. the chord is slack by `(q−d)(q+1−d) ≥ 2(q−d)` at a
vertex of degree `d` (`chordDef`). Fix `q` and split:

* if every degree is at most `q`, then `2m ≤ n·q` (first branch of the `max`);
* otherwise some vertex `v` has `d(v) ≥ q+1`. Apply the *slack* chord on `N(v)` and the plain
  chord outside it, and add:
  `(2q+1)·2m + 2q·d(v) ≤ ∑ d(w)² + n·q(q+1) + 2·∑_{u ∼ v} d(u)`.
  Now `∑_{u ∼ v} d(u) ≤ n − 1` (the per-vertex count), `∑ d(w)² ≤ n(n−1)` (V001) and
  `d(v) ≥ q+1`, giving
  `(2q+1)·2m + 2·q(q+1) ≤ n(n−1) + n·q(q+1) + 2(n−1)`.

Against V002 the gain in `(2q+1)·2m` is `2·(q(q+1) − (n−1))`, which for `q ≈ √(n−1)` is of order
`√n`, whereas V003's gain was the constant `2`. Equivalently: the `q+1` or more neighbours of `v`
have degrees summing to at most `n − 1`, so their total shortfall below `q` is at least
`q(q+1) − (n−1)`, and each unit of shortfall buys `2`.

This improves V003 at **31 of the first 400 values of `n`** (V003 itself improved V002 at 12):
`19, 51, 69, 85, 86, 123, 129, 151, 172, 173, 198, 200, 227, 228, 231, 234, 236, 238, 265, 292,
293, 297, 298, 326, 328, 330, 363, 364, 367, 368, 373`, each by `1`. Widening the search over `q`
beyond the three values nearest `√(n−1)` gains nothing (checked for `q ≤ 40`, `n ≤ 400`).

Witness `n₀ = 19`: `40` → `39` (true value `f(19) = 38`).

## V005 attempt — baseline claude-opus-5 (not accepted: no gain, recorded as a dead end)

Idea: in V004's case split, the threshold of the split and the chord parameter play independent
roles, so free them: for **any** `t`, either every degree is at most `t` and `2m ≤ n·t`, or some
vertex `v` has `d(v) ≥ t + 1` and the slack chord at `q` on `N(v)` gives
`(2q+1)·2m + 2q(t+1) ≤ n(n−1) + n·q(q+1) + 2(n−1)`, i.e.

```
bnd(n, q, t) = max( ⌊n·t/2⌋ , ⌊ ( n(n−1) + n·q(q+1) + 2(n−1) − 2q(t+1) ) / (2(2q+1)) ⌋ )
```

V004 is `t = q`; lowering `t` to `q − 1` drops the first branch by `n/2` and raises the second by
at most `1`, so it looked promising, and against V004's own `v` component it does improve — at
`n = 9, 49, 121, 225, 361, 529, 729, 961, 1225, 1521, 1849`, i.e. at `n = (4j+3)²`, by `1`.

**But it never improves the record.** Against the full chain `min(V001, V002, V003, V004)` the
gain is zero for every `n ≤ 800` even with `q` and `t` both searched over a window of width `7`
around `√(n−1)`: at exactly those `n` the V002/V003 components are already at least as small.
The Lean proof was written and compiles (it is V004's proof with `q + 1` replaced by `t + 1` in
the split and `hq1`); only `strict` fails, because no witness exists. Do not retry this
parametrisation — the degree-sequence relaxation really is exhausted, as V002's note said, and
the remaining slack is all in the *per-vertex* constraint.

The next version therefore has to use `Σ_{u ∼ x} d(u) ≤ n − 1` at more than one vertex at a time
(see the last section): a relaxation of the integer program below, e.g. "if `k` vertices have
degree `≥ s+1` then at least `k'` vertices have degree `≤ s−1`", is the first thing that is not
already implied by `Σ d(w)² ≤ n(n−1)` plus a single high-degree vertex.

## V005 — trial claude-fable

Bound: `record n = min( V004.record n, bnd(n, s) )` with `s = ⌊√(n−1)⌋`, `ρ = n − 1 − s²` and
`D = ρ(2s − 1) − 1`, where

```
bnd(n, q) = ⌊ ( D·n·q + n·ρ·(ρ−1) ) / (2·D) ⌋        (D ≠ 0; otherwise C(n,2))
```

i.e. **`2m ≤ nq + ⌊ nρ(ρ−1) / (ρ(2q−1) − 1) ⌋`**, against V002's `2m ≤ nq + ⌊nρ/(2q+1)⌋`.
Only `q = s` is folded in (at `s + 1` the residue is `0`, at `s − 1` it exceeds `q`).

This is the relaxation of the integer program that the previous report asked for. V004 applied
the per-vertex count `∑_{u ∼ x} d(u) ≤ n − 1` at *one* vertex of degree `≥ q + 1`; V005 sums
it over the set `H` of **all** such vertices and double counts:
`∑_{x ∈ H} ∑_{u ∼ x} d(u) = ∑_u d(u)·a(u)` with `a(u) = #(N(u) ∩ H)`. With `h = #H`,
`T = ∑ (d(u) − q)⁺`, `S = ∑ (q − d(u))⁺`:

* `∑_u a(u) = ∑_{x ∈ H} d(x) = qh + T`, so
  `q(qh + T) ≤ ∑ d(u)a(u) + ∑ (q − d(u))⁺a(u) ≤ h(n − 1) + (q − 1)S`, because a vertex of
  degree `< q` has `a(u) ≤ d(u) ≤ q − 1`. Every high-degree vertex needs `q − ρ` units of
  shortfall in its neighbourhood, and each low-degree vertex can serve at most `q − 1` of
  them: `(q − 1)S ≥ (q − ρ)T` (using `h ≤ T`).
* the degree identity `2m + S = nq + T`;
* the chord sum with its slack, `(2q + 1)·2m + 2S ≤ n(n − 1) + nq(q + 1)` (V004's `chordDef`
  summed over all vertices, plus `∑ d² ≤ n(n − 1)`).

Eliminating `S`, `T`, `h` (multiply the chord sum by `ρ − 1` and add twice the other two)
gives `D·2m ≤ D·nq + nρ(ρ − 1)`. In the underlying LP the optimum has every low degree
`q − 1` and every high degree `q + 1`, which is what the pointwise estimates reproduce.

The gain over V002 in `2m` is about `n(2q + 1 − 2ρ)/(4q²) ≈ (2q + 1 − 2ρ)/4` whenever
`ρ < q` — about half of all `n` — so it grows like `√n`; at `ρ = 1` (`n = q² + 2`) the bound
collapses to `2m ≤ nq`. V005 improves V004 at **141 of the first 400** `n`, **324 of the first
800**, and **876 of the first 2000**; the gain is `1` up to `n = 82`, `2` from `n = 83`, `5`
from `n = 443`, and `10` at `n = 1943`. It is tight at `n = 11` (`f(11) = 16`). Chosen because
it is the first bound on this track whose gain is unbounded, and the proof reuses all four
earlier lemmas (`V001.sum_sq_degree_le`, `V002.chord`, `V003.nbr_sum_le`, `V004.chordDef`).
The whole file costs 46536 heartbeats, `arith` (the `ℤ` elimination by `nlinarith`) 29434.

Witness `n₀ = 11`: `17` → `16`, the exact value `f(11) = 16`.

## V006 — trial claude-fable

Bound: `record n = min( V005.record n, boundA n, boundB n )`, where each `bound` is a
**linear-programming certificate evaluated by the record itself**. With `N = n − 1`,
`q = ⌊√N⌋`, `ρ = N − q²`: a certificate is a concave nondecreasing `ψ`, the minimum of five
lines `x ↦ (S_k x + I_k)/Q` (`S_k, I_k, Q ∈ ℕ`), and

```
Λ = max_{0 ≤ d ≤ N} ( 2·d·ψ(N/d) + Q·d − 2·d·ψ(d) ),      m ≤ ⌊ n·Λ / (2Q) ⌋ .
```

**Why it is true (all of `Proof.lean`, `cert_main`).** For a vertex `v` of degree `d`, let
`ℓ = S x + I` be a line attaining `ψ(N/d)`. Then
`∑_{u ∼ v} ψ(d(u)) ≤ ∑_{u ∼ v} ℓ(d(u)) = S·∑_{u ∼ v} d(u) + I·d ≤ S·N + I·d = d·ψ(N/d)`
by the per-vertex count and `S ≥ 0`. Summing over `v`, double counting
`∑_v ∑_{u ∼ v} ψ(d(u)) = ∑_u d(u) ψ(d(u))`, and using the defining inequality of `Λ` at each
vertex, `2Q·m ≤ n·Λ`. This is the dual of the LP over degree classes (numbers of vertices per
degree and of edges per degree pair, with the per-class neighbourhood sums as constraints);
the weight on the constraint of a vertex of degree `d` is the slope of `ψ` at `N/d`. Because
the theorem holds for *any* lines and `Λ` is computed, the Lean proof contains no inequality
about the specific lines at all — everything is in ℕ and closes with `omega`.

**Where the lines come from.** Numerically (scipy/HiGHS) the class LP is attained by degrees
`q − 1, q, q + 1` for `q ≤ 20` and by `q − 2, …, q + 2` beyond, and its dual is always
realised by a `ψ` with breakpoints at `q − 1, q, q + 1, q + 2` (checked exactly against the
LP for `n ≤ 3631`). Solving the tight constraints gives:

* **A** (tight at `d = q − 1, q, q + 1, q + 2`), `D' = (q − 1) + ρ(3q − 2 − ρ)`,
  `c = q − 2 − ρ`: slopes `(q − 4 + 3ρ(q − 3 − ρ))/(2D'c)`, `(ρ + 1)/D'`, `(ρ − 1)/(2D')`,
  `0`. Its `Λ` is exactly `2m ≤ nq + nρ(ρ − 1)/D'` — V005's bound with the denominator
  `ρ(2q − 1) − 1` raised by `(q − ρ)(ρ + 1)`. In the LP optimum the vertices of degree `q`
  matter: they absorb at most `ρ` high-degree neighbours each, so the high-degree vertices
  cannot all lean on them.
* **B** (tight at `d = q − 2, …, q + 2`): a rational solution with a quartic common
  denominator (`Def.lean`); it takes over for `q ≳ 25`, where the LP uses degrees `q ± 2`.

All formulas use truncated subtraction, so outside their regime they still define *some*
lines (a valid, weaker bound) and `V005` takes over through the `min`.

**Gain.** Of order `n` in `2m` for `2 ≤ ρ ≲ q − 3` (about `n/20` at `ρ ≈ q/2`). V006
improves V005 at **1171 of the first 3000** `n` (first `n = 85`), by up to `10` for
`n ≤ 400`, `21` for `n ≤ 900`, `33` for `n ≤ 1600`, `49` for `n ≤ 2500`, `57` for
`n ≤ 3000`, and it agrees with the degree-class LP optimum wherever checked. Chosen because
it exhausts the degree-class relaxation of the per-vertex constraints in one step, with a
proof (22881 heartbeats, 9975 of them the witness) that is *shorter* than V005's.

**Cost.** Evaluating the record by `decide +kernel` costs about `1400` heartbeats at
`n = 105`, `10400` at `n = 410`, `43000` at `n = 916` (a maximum over `N + 1` degrees).
Later witnesses should stay below about `n = 1500`, or the next version should restrict
the maximum to the degrees near `q` after proving the others are dominated.

Witness `n₀ = 410`: `4142 → 4132` (`q = 20`, `ρ = 9`).

## Parked: V007 via typed second-neighbourhood constraints (trial claude-fable)

Not submitted; no record directory was created (the Challenge is open at `V007`). This is the
next substantial step and the numbers below say it is large; what is missing is a certificate
form that a record can evaluate cheaply. Everything here is in the session's scratch
directory under `.lake/scratch/ExGirthFive-Upper/` (Python scripts, a virtual environment
`venv/` with scipy and sympy).

**The new constraint.** For every vertex `x` and every set `B ⊆ V`, with `a_B(v) = #(N(v) ∩ B)`:

> `∑_{u ∼ x} a_B(u) + a_B(x) ≤ |B| + [x ∈ B]·(d(x) − 1)`.

Proof: the sets `N(u) ∖ {x}` (`u ∼ x`), `N(x)` and `{x}` are pairwise disjoint (girth 5), so
their traces on `B` have total size at most `|B|`, and `#(N(u) ∩ B ∖ {x}) = a_B(u) − [x ∈ B]`.
With `B = V` it is V003's `nbr_sum_le`. With `B = H = {d ≥ q + 1}`, `h = #H`, it splits the
per-vertex count into an `H`-part (`≤ h + [x ∈ H](d − 1)`) and an `R`-part (`≤ n − h + …`).
Formalising it is a small variant of `nbr_sum_le`.

**How much it is worth.** The *typed LP* (types `(d, a_H)`, `h` fixed, edge variables per pair
of types, degree and `a_H` consistency, both typed constraints per type; `typedlp.py`) is
consistent with every known value `n ≤ 53` (`typedsmall.py`) and is exact at `n = 19, 20, 50`.
Its optimum over `h` (`typedland.py`) compared with V006, as `2m − nq`:

| q = 10, ρ | 2 | 4 | 5 | 7 | 9 | 11 | 14 | 16 | 19 | 20 |
|---|---|---|---|---|---|---|---|---|---|---|
| typed LP | 0 | 0 | 1.8 | 9.0 | 18.6 | 32 | 54.5 | 72 | 100 | 110 |
| V006 | 2 | 12 | 16 | 34 | 46 | 58 | 76 | 88 | 108 | 114 |

| q = 20, ρ | 2 | 8 | 12 | 14 | 18 | 22 | 26 | 30 | 36 | 40 |
|---|---|---|---|---|---|---|---|---|---|---|
| typed LP | 0 | 0 | 0 | 17.8 | 59.3 | 108 | 167.5 | 234 | 341 | 418 |
| V006 | 6 | 54 | 94 | 118 | 182 | 226 | 270 | 314 | 382 | 430 |

So `2m ≤ nq` holds for `ρ ≤ 4` (`q = 10`) and `ρ ≤ 12` (`q = 20`), roughly `ρ ≲ 0.6q`, and
the gain persists over the whole range: in edges, `6` at `n = 105`, `32` at `n = 410`, `51`
at `n = 415`, `40` at `n = 431`. The optimal configurations use only degrees `q, q + 1` and a
few of degree `q − 3`, with specific numbers of `H`-neighbours.

**The obstruction.** `h` is global. In any linear certificate the `+h` on the right of the
`B = H` constraint at `x`, weighted by `β(x)`, sums to `(∑_x β(x))·h`, a product of two graph
sums; only a uniform `β` linearises it, and every `h`-free family tested collapses to V006
(`potential_hfree.py`: planes with `g^H ≤ g^R`; `potential_c.py`: a global constant `c` with
penalty `c·n` on `H`-vertices; `simplefam.py`: V006's potential plus one typed weight per
class — all return exactly V006's values, e.g. `531` at `n = 105`, `4209` at `n = 415`). The
gain needs `h` in both directions (the `B = H` constraints bound `h` from below, the `B = R`
ones at `H`-vertices from above), which pairs *different* vertices:
`|B₂(x) ∩ H| + |B₂(y) ∩ R| ≤ n` for all `x, y`.

**What works at fixed `h`.** The potential form generalises: for each vertex `x` a plane
`P_x(τ') = c + g^H·a' + g^R·(d' − a') + γ·[τ' ∈ H]` on the type space with `g^H, g^R ≥ 0` and
`Ψ ≤ P_x`, giving `∑_{u ∼ x} Ψ(τ(u)) ≤ d·c + g^H·K_H(x) + g^R·K_R(x) + γ·a_H(x)` with
`K_H = h + [H](d − 1) − a`, `K_R = (n − h) + [R](d − 1) − (d − a)`; then a requirement per
type as in V006 (`potential2d.py`). At fixed `h` it is within a few edges of the typed LP
(`n = 105, h = 10`: `526.6` vs `524.5`; `n = 415, h = 56`: `4169` vs `4159`; `n = 112, h = 32`:
`576.1` vs `576`). Hence a record has to compute `max_h bound(h)`. Per `h` the requirement
is affine in `a` plus convex, so only `a ∈ {0, d}` matter, but the loop over `h` multiplies
V006's cost by `n`: too much for the kernel. With the planes frozen on `h`-ranges the
requirement is affine in `h` on each range, so only the range endpoints need evaluating: with
about ten ranges the cost is an estimated `80k` heartbeats at `n = 100` (V006 costs `1.4k`
at `n = 105`), feasible, but it needs closed forms for the planes in `(q, ρ, h)` on each
range, which were not derived (the LP duals, `typeddual.py`, are degenerate and unstructured).

**Suggested routes.** (a) Derive the frozen-range planes symbolically from the tight types of
the fixed-`h` potential LP (the tight set is small: types `(q, a)`, `(q + 1, a')` and one
low-degree type) and evaluate the record as `max` over range endpoints. (b) Look for a direct
proof of `2m ≤ nq` for `ρ ≤ c·q` from the pair constraint above; the LP says `c ≈ 0.6`, and
even `c = 1/3` would improve V006 at a quarter of all `n` by about `(ρ − 1)q/6` edges.
(c) Cheaper first: formalise the constraint for `B = H` and use it only at the vertices of
degree `≥ q + 2` (they need `2q − ρ` units of shortfall from `≤ q + 2` neighbours), which does
not involve `h` at all when combined with V006's planes at those degrees.

## Values

| n | 5 | 10 | 14 | 15 | 19 | 20 | 25 | 32 | 50 | 100 | 200 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| `V000 = C(n,2)` | 10 | 45 | 91 | 105 | 171 | 190 | 300 | 496 | 1225 | 4950 | 19900 |
| `V001` | 5 | 15 | 25 | 28 | 40 | 43 | 61 | 89 | 175 | 497 | 1410 |
| `V002` | 5 | 15 | 25 | **27** | 40 | 43 | 61 | **88** | 175 | 497 | 1410 |
| `V003` | 5 | 15 | 25 | 27 | 40 | 43 | 61 | 88 | 175 | 497 | 1410 |
| `V004` | 5 | 15 | 25 | 27 | **39** | 43 | 61 | 88 | 175 | 497 | **1409** |
| `V005` | 5 | 15 | 25 | 27 | 39 | 43 | 61 | 88 | 175 | 497 | **1407** |
| `V006` | 5 | 15 | 25 | 27 | 39 | 43 | 61 | 88 | 175 | 497 | **1404** |
| true `f(n)` | 5 | 15 | 23 | 26 | 38 | 41 | 57 | 85 | 175 | — | — |

Where V005 gains (`n − 1 = q² + ρ`, `ρ` small):

| n | 11 | 51 | 102 | 103 | 227 | 402 | 403 |
|---|---|---|---|---|---|---|---|
| `V004` | 17 | 179 | 512 | 519 | 1705 | 4024 | 4039 |
| `V005` | **16** | **178** | **510** | **517** | **1702** | **4020** | **4035** |
| `V006` | 16 | 178 | 510 | **516** | 1702 | 4020 | **4033** |
| true `f(n)` | 16 | 176 | — | — | — | — | — |

Where V006 gains (`ρ` in the middle of its range):

| n | 85 | 105 | 200 | 230 | 300 | 410 | 450 | 916 | 1621 | 2526 |
|---|---|---|---|---|---|---|---|---|---|---|
| `V005` | 387 | 533 | 1407 | 1737 | 2591 | 4142 | 4763 | 13848 | 32615 | 63456 |
| `V006` | **385** | **531** | **1404** | **1733** | **2583** | **4132** | **4753** | **13827** | **32580** | **63406** |

`V003` differs from `V002` at twelve `n ≤ 400` (first `n = 18`); `V004` differs from `V003` at
thirty-one `n ≤ 400` and at **67 of the first 800** `n` (first `n = 19`), always by `1`.

(true values: OEIS A006856, reporting only.)

V001–V006 are accepted; the Challenge is open at `V007`. The V005 *attempt* of the earlier
submitter was abandoned because it improved nothing; the accepted V005 is the one above.

## What the next improvement would take

- **First: the typed second-neighbourhood constraints** of the parked section above; the
  typed LP gives `2m ≤ nq` for `ρ ≲ 0.6q` and gains of order `n` in `2m` everywhere else.
  The single obstacle is a certificate that does not need a loop over `h = #{d ≥ q + 1}`.
- **The degree-class relaxation is exhausted by V006**: its record computes the exact LP
  optimum of the class LP wherever checked (`n ≤ 3631`); do not spend time on other
  degree-sequence arguments.
- **Cost of V006's record.** Evaluating it by `decide +kernel` costs about `10k` heartbeats
  at `n = 410` and `43k` at `n = 916`, so keep witnesses below about `n = 1500`, or restrict
  the maximum to degrees near `q` after proving the others are dominated.

- **Not the constant.** Anything of the form `c·n^{3/2}` with `c < ½` would settle Erdős #573.
  Every realistic next step is a lower-order gain.
- **The minimum-degree recursion is dead — checked, do not spend time on it.** V002's note
  suggested folding in `f(n) ≤ f(n−1) + δ` with `δ ≤ ⌊√(n−1)⌋`, at the cost of formalising
  vertex deletion. It **never** improves the record: `min( V002(n), R(n−1) + ⌊√(n−1)⌋ )` equals
  `V002(n)` for every `n ≤ 800`. The reason is asymptotic, not accidental — `d/dn [½n√(n−1)] ≈
  ¾√n`, strictly less than the increment `√(n−1)` the recursion allows, so the recursion loses
  ground at every step and can only propagate a gain that is already there. The same holds for
  the sharper `δ ≤ ⌊2m/n⌋` version and for deleting a whole closed neighbourhood
  (`m ≤ f(n−1−Δ) + (n−1)`, which is off by `+¼n`). The plumbing for vertex deletion is cheap
  anyway if ever needed: `SimpleGraph.comap (Fin.succAbove v)` for the induced subgraph and
  `SimpleGraph.card_edgeFinset_deleteIncidenceSet` for the edge count.
- **The per-vertex count `Σ_{u ∼ x} d(u) ≤ n − 1` has much more in it than V003 extracts.**
  V003 only uses its consequence `Δ·δ ≤ n − 1`. The full constraint says that for every `x`, the
  sum of the `d(x)` *smallest* degrees among the other `n − 1` vertices is at most `n − 1`. The
  integer program
  > maximise `Σ d(w)` subject to `Σ d(w)² ≤ n(n−1)` and, for every `w`, the sum of the `d(w)`
  > smallest other degrees is `≤ n − 1`

  is strictly below V002 at a large fraction of `n` — e.g. at `n = 19` it gives `2m ≤ 76`
  (`m ≤ 38`) against V002's `m ≤ 40`, because a degree sequence mixing `s` and `s+1` is
  infeasible whenever `n − 1 < s(s+1)`, which is about half of all `n`. Formalising a usable
  relaxation of it — say "at most `k` vertices have degree `≥ s+1`, and then at least `k'`
  vertices have degree `≤ s−1`" — is where the next substantial version lies. Two weaker
  relaxations were computed and rejected as not worth their proof length: pulling out the
  maximum-degree vertex and Cauchy–Schwarzing its neighbourhood gains at `13` of the first `158`
  `n`, barely more than V003's `12/400`.
- **Sharper degree-sequence LPs** (Abajo–Diánez et al. 2017) mix the counting above with parity
  and with the structure of the neighbourhoods of high-degree vertices.
- **Problems hit.** `Nat.sqrt` does not reduce under plain `decide` (well-founded recursion),
  only under `decide +kernel`; the fuel gate uses the latter, so this is fine. `omega` refuses
  any nonlinear atom, so the degree arithmetic has to be assembled with `calc` and `Nat.add_le_add`
  rather than discharged wholesale; `Finset.card_sdiff` in this Mathlib has no subset hypothesis
  (it is `#(s \ t) = #s − #(t ∩ s)`), and `G.loopless` is a `Std.Irrefl` instance, not a
  function. Everything else went through at a small fraction of the heartbeat budget: V003 costs
  `18348` heartbeats in all, against a limit of `200000`.
