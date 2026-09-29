# Ramsey3, upper track — report

`f(k) = R(3,k)`: the least `N` such that every 2-colouring of the edges of `K_N` has a triangle
in the first colour or a `K_k` in the second. `nMin = 2`.

## What the literature gives

**Exact small values** (Radziszowski, *Small Ramsey Numbers*, Electron. J. Combin. Dynamic
Survey DS1, revision #17, 2021; OEIS A000791):

| k | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|---|----|
| R(3,k) | 3 | 6 | 9 | 14 | 18 | 23 | 28 | 36 | 40–41 |

`R(3,10)` is open; the upper bound `41` is Goedgebeur–Radziszowski (2013), the lower bound `40`
is Exoo. Beyond that DS1 lists `R(3,11) ≤ 47`, `R(3,12) ≤ 53`, … all from exhaustive
computation on triangle-free graphs, none of them from a closed form.

**Closed forms valid for every k.**

- Erdős–Szekeres (1935), `R(s,t) ≤ C(s+t-2, s-1)`; at `s = 3` this is `C(k+1,2) = k(k+1)/2`.
  This is the seed record V000.
- Greenwood–Gleason (1955) sharpened the Erdős–Szekeres recursion: `R(s,t) ≤ R(s-1,t) +
  R(s,t-1) - 1` whenever `R(s-1,t)` and `R(s,t-1)` are both even. Run from `R(3,2) = 3` with
  `R(2,k) = k`, the saving applies at every even `k`, and the closed form of the resulting
  recursion is `R(3,k) ≤ (k² + 3)/2` in natural division. This is V001 below.
- Ajtai–Komlós–Szemerédi (1980), *A note on Ramsey numbers*, JCTA 29: `R(3,k) = O(k²/log k)`,
  the first bound of the right order.
- Shearer (1983), *A note on the independence number of triangle-free graphs*, Discrete Math.
  46: `R(3,k) ≤ (1 + o(1)) k² / log k`, still the best known leading constant.
- Kim (1995), *The Ramsey number R(3,t) has order of magnitude t²/log t*, Random Structures
  Algorithms 7, gives the matching lower order; Fiz Pontiveros–Griffiths–Morris (2020) and
  Bohman–Keevash pin the lower constant at `(1/4 - o(1)) k²/log k`.

So the *order* is settled and the open question is the constant between `1/4` and `1`. Every
bound in the `k²/log k` range needs the AKS/Shearer independence-number estimate for
triangle-free graphs, which is a genuine research formalisation; everything reachable by the
Erdős–Szekeres recursion sits at `k²/2`.

## Starting record

V000 (SqueezeBench seed): `record k = C(k+1, 2) = k(k+1)/2`, from `Ramsey.forcesOn_choose 2 (k-1)`.
Exact at `k = 2` and `k = 3`; `45` against `36` at `k = 9`.

## V001 — baseline claude-opus-5

**Bound.** `record = minWith V000.record v` with

```
v k = (k * k + 3) / 2        -- natural division
```

so `v k = k²/2 + 1` for even `k` and `(k²+3)/2` for odd `k`. The `minWith` only matters at
`k = 0, 1`, below `nMin`, where `(k²+3)/2` exceeds the seed; from `k = 2` on the record *is*
`(k²+3)/2`.

**Idea.** The parity refinement of Erdős–Szekeres, proved from scratch as
`forcesOn_step_parity` in `Proof.lean`. Suppose no colouring of `K_N` with `N = M + N' - 1`
vertices has a red `K_{s+1}` or a blue `K_{t+1}`, where `M` forces `(s, t+1)` and `N'` forces
`(s+1, t)`. Applying the two hypotheses inside the red and the blue neighbourhood of a vertex
(lemmas `deg_bound`, `codeg_bound`) gives red degree `< M` and blue degree `< N'` at *every*
vertex; the two degrees sum to `N - 1 = M + N' - 2`, so both inequalities are tight everywhere
and the red graph is exactly `(M-1)`-regular on `M + N' - 1` vertices. When `M` and `N'` are
both even that is an odd-regular graph on an odd number of vertices, and
`SimpleGraph.sum_degrees_eq_twice_card_edges` — the handshake lemma — forbids it.

At `s = 2`, `t = k` the first hypothesis is `M = k + 1` (`R(2,k+1) = k+1`, from
`forcesOn_choose 1 k`) and the second is the bound already proved for `R(3,k)`. `k + 1` is even
exactly when `k` is odd, and `(k²+3)/2` is then even as well, so the saving lands at every step
from an odd `k` to an even `k + 1` — infinitely many, and the accumulated saving against V000
is `⌊(k-2)/2⌋`, which grows without bound.

**Why this bound.** It improves the seed at every `k ≥ 4`, by a margin that grows linearly,
and it is the exact closed form of the best recursion available without the AKS machinery. It
also makes the record exact at `k = 4` (`9`) and `k = 5` (`14`), so together with the lower
track it pins two more values of `R(3,k)` in principle.

**Witness.** `n₀ = 9`: `45 → 42`.

**Cost.** 18491 heartbeats in all (limit 200000); heaviest declaration
`forcesOn_step_parity` at 8813.

## Values

| k | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 20 |
|---|---|---|---|---|---|---|---|---|----|----|
| V000 `k(k+1)/2` | 3 | 6 | 10 | 15 | 21 | 28 | 36 | 45 | 55 | 210 |
| **V001 `(k²+3)/2`** | **3** | **6** | **9** | **14** | **19** | **26** | **33** | **42** | **51** | **201** |
| true `R(3,k)` | 3 | 6 | 9 | 14 | 18 | 23 | 28 | 36 | 40–41 | ≥ 92 (DS1) |

V001 is exact at `k = 2, 3, 4, 5`.


## V002 — trial claude-fable

**Bound.** `record = minWith V001.record v` with

```
v k = (k - 1) * q(k-1) / p(k-1) + 1        -- natural division, p(d)/q(d) = f(d)
f 0 = 1,   f d = (1 + (d² - d) f(d-1)) / (d² + 1)
```

i.e. `R(3,k) ≤ ⌊(k-1) / f(k-1)⌋ + 1` with Shearer's sequence `f`, kept in `Def.lean` as a pair
of naturals (`shearer d = (p d, q d)`, `q d = Π (i²+1)`) so that the record is kernel
arithmetic. `f(d) ~ log d / d`, so the record is `(1 + o(1)) k² / log k`.

**Idea.** Shearer's degree-sequence theorem (J. B. Shearer, *A note on the independence number
of triangle-free graphs, II*, J. Combin. Theory Ser. B 53 (1991), 300–307): a triangle-free
graph with degrees `d₁, …, dₙ` has an independent set of size at least `Σᵢ f(dᵢ)`. With no
independent `k`-set every neighbourhood is independent, so every degree is at most `k - 1`;
`f` is decreasing, so `n · f(k-1) ≤ α ≤ k - 1`, and `⌊(k-1)/f(k-1)⌋ + 1` vertices force.

The theorem is proved from scratch in `Proof.lean` (`shearer_indep`), by induction over vertex
subsets `S` of one fixed graph rather than over induced subgraphs: degrees are `|N(u) ∩ S|`,
deleting `N[v]` is a filter, and the whole argument is a computation in ℚ with no logarithm.
Deleting `N[v]` lowers the degree of each remaining `u` by `c = |N(u) ∩ N(v)|`, and by convexity
of `f` this costs at most `c · del(deg u)` with `del d = f(d-1) - f(d)`; summing the resulting
requirement over all `v` and using the walk count `Σ_{x ∉ N[u]} |N(u) ∩ N(x)| = Σ_{w ∈ N(u)}
(deg w - 1)` (the only use of triangle-freeness), the rearrangement inequality for the
decreasing `del`, and the identity `(1 + d) f(d) - d(d-1) del(d) = 1`, some `v` satisfies the
local requirement. Convexity and monotonicity of `f` come from the crude bound
`f(d) ≥ 3/(2d+5)`, proved by induction.

**Why this bound.** It is the best known upper bound on `R(3,k)` in closed/recursive form — the
constant `1` in `(1 + o(1)) k²/log k` has not been improved as of 2026 (the lower-bound constant
was raised to `1/2` by Hefty–Horn–King–Pfender, arXiv 2510.19718) — and it beats V001 at every
`k ≥ 7`, by a margin that grows like `k²/2 - k²/log k`. It supersedes all three routes listed
by the earlier sessions, including the "structural elimination" route, by a wide margin.

**Witness.** `n₀ = 10`: `51 → 46`.

**Cost.** 52988 heartbeats in all (limit 200000); heaviest declaration `del_succ_succ_le` at
9608, then `rearrange` 8926 and `forcesOn_v` 8403. The record evaluates at `k = 100` well
within the fuel budget (`q(99)` has about 300 digits, but the kernel's GMP arithmetic makes this
cheap).

## Values (updated)

| k | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 20 | 50 | 100 |
|---|---|---|---|---|---|---|---|---|----|----|----|----|----|-----|
| V000 `k(k+1)/2` | 3 | 6 | 10 | 15 | 21 | 28 | 36 | 45 | 55 | 66 | 78 | 210 | 1275 | 5050 |
| V001 `(k²+3)/2` | 3 | 6 | 9 | 14 | 19 | 26 | 33 | 42 | 51 | 62 | 73 | 201 | 1251 | 5001 |
| **V002 Shearer** | **3** | **6** | **9** | **14** | **19** | **25** | **32** | **39** | **46** | **55** | **63** | **153** | **746** | **2525** |
| true `R(3,k)` | 3 | 6 | 9 | 14 | 18 | 23 | 28 | 36 | 40–41 | 47–50 (DS1 ≤ 53 at 12) | | ≥ 92 | | |

V002 is exact at `k = 2, 3, 4, 5`; at `k = 6` it equals V001 (`19` against `18`).


## V003 — trial claude-fable

**Bound.** `record = minWith V002.record v` with

```
v k = min over r < k of cand (k-1) r (V002.v k)
cand D r fb = if A ≤ B·D then fb else max (4D) (⌊((D-1) q(r+1) + A (D+1) - 2 B D²) / (A - B D)⌋ + 1)
B = p(r)((r+1)² + 1) - p(r+1),   A = p(r)((r+1)² + 1) + r B        -- β = B/q(r+1), a = A/q(r+1)
```

i.e. the smallest `n` with `1 + a (n - 1 - D) - β D (n - 2D) > D` for the best secant point `r`,
where `β = f(r) - f(r+1)` and `a = f(r) + r β`.

**Idea.** A second-order refinement of Shearer. Delete a closed neighbourhood `N[v]`: the rest
has `n - 1 - d_v` vertices and `e - Σ_{w ∈ N(v)} d_w` edges, hence a *lower* average degree than
`D` (about `D - log D` in the extremal case). Apply Shearer's theorem to it through the secant
line of `f` between `r` and `r + 1` (below `f` by convexity), so that the bound is affine in the
edge count, average over `v` (`Σ_v 2e(G[W_v]) = Σ_u d_u (n - 2 d_u)`), and minimise the quadratic
in each degree over `0 ≤ d_u ≤ D`, which sits at `d_u = D` when `n ≥ 4D`:
`α ≥ 1 + a(n - 1 - D) - β D (n - 2D)`. Shearer's own proof loses exactly the convexity gap
between the tangent of `f` at `D` and its value at the lower average degree, which is why this
gains: second order, about `log k` in `n`, i.e. `1` or `2` at most `k ≥ 8` and `0` at a few `k`
(`10, 12, 17`). Everything is in `Proof.lean` on top of V002's lemmas: `secant`,
`deletion_bound`, `cand_arith`, and a fold lemma for the minimum over `r`.

**Why this bound.** After V002 the leading term is the best known; this is the natural next
step that still improves infinitely many `k` (from `k = 8` on, most `k`), at low cost given the
V002 infrastructure. The point improvements at `k = 8` (`32 → 31`) and `k = 9` (`39 → 38`) are
the first two.

**Witness.** `n₀ = 8`: `32 → 31`.

**Cost.** 90110 heartbeats in all (limit 200000); heaviest declaration `cand_arith` at 54798
(three `nlinarith` calls), then `deletion_bound` at 13533. The fold over `r < k` evaluates the
record at every `k ≤ 100` within the fuel budget.

## Values (updated after V003)

| k | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 20 | 28 | 40 | 100 |
|---|---|---|---|----|----|----|----|----|----|----|----|----|----|-----|
| V001 `(k²+3)/2` | 26 | 33 | 42 | 51 | 62 | 73 | 86 | 99 | 114 | 129 | 201 | 393 | 801 | 5001 |
| V002 Shearer | 25 | 32 | 39 | 46 | 55 | 63 | 73 | 83 | 93 | 104 | 153 | 273 | 506 | 2525 |
| **V003 deletion** | **25** | **31** | **38** | **46** | **54** | **63** | **72** | **82** | **92** | **103** | **152** | **271** | **504** | **2523** |
| true `R(3,k)` | 23 | 28 | 36 | 40–41 | ≤ 47 | ≤ 53 | | | | | | | | |


## V004 — trial claude-fable

**Bound.** `record = minWith V003.record v` with

```
v k = the least N₀ ∈ {V-3, V-2, V-1} with check (k-1) r N₀ for some r < k, else V   (V = V003.v k)
check D r N₀ :  2 ≤ D  ∧  5D+1 ≤ N₀  ∧  B·D < A  ∧
                (D-2) q' m² + B X m² + A m X < A m² (m-1) + 2 B X²
                where m = N₀ - 1 - D,  X = D (N₀ - 2D),  q' = q(r+1),  A = q' a,  B = q' β
```

i.e. `1 + q(m, X/m) > D` with `q(m, x) = 1 + a (m - 1 - x) - β x (m - 2x)`, `β = f(r) - f(r+1)`,
`a = f(r) + r β`, checked at the candidate `N₀`.

**Idea.** A second level of the deletion argument. For the vertex `v` whose neighbours have the
largest degree sum, `G - N[v]` has at least `m = n - 1 - D` vertices and degree sum at most
`X = D (n - 2D)` (since `Σ_{w ∈ N(v)} deg w ≥ (Σ deg)² / n²`). The V003 identity applied inside
`G - N[v]`, with Cauchy–Schwarz on its degrees instead of the per-vertex minimisation, gives an
independent set of size `q(m', σ/m')`, and monotonicity of `q` gives `α ≥ 1 + q(m, X/m)` for
`n ≥ 5D + 1`. The record checks this certificate at `N₀` and the proof restricts a larger graph
to an induced subgraph on exactly `N₀` vertices, so no monotonicity in `n` is needed. This
captures exactly the gain of a full two-level argument (verified numerically in the regular
case) at a fraction of the formalisation cost: `1` at `k = 12, 14, 17, 19–38, 40, 80`, `2` at
`k = 39, 50, 60, 100`.

**Why this bound.** After V003 the only remaining elementary gains are second order; this is the
cheapest one that improves infinitely many `k`, and it reuses all of V002/V003.

**Witness.** `n₀ = 12`: `63 → 62`.

**Cost.** 67876 heartbeats in all; heaviest `q_le_of_ramsey` 31453. A first version that kept
the ℕ certificate inequality in the context of `omega`/`linarith` calls cost 145000 for one
declaration; separating the graph argument from the certificate wrapper fixed it.

## Values (updated after V004)

| k | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 17 | 19 | 20 | 28 | 39 | 40 | 50 | 100 |
|---|---|---|----|----|----|----|----|----|----|----|----|----|----|----|-----|
| V001 `(k²+3)/2` | 33 | 42 | 51 | 62 | 73 | 86 | 99 | 146 | 182 | 201 | 393 | 762 | 801 | 1251 | 5001 |
| V002 Shearer | 32 | 39 | 46 | 55 | 63 | 73 | 83 | 115 | 140 | 153 | 273 | 483 | 506 | 746 | 2525 |
| V003 one deletion | 31 | 38 | 46 | 54 | 63 | 72 | 82 | 115 | 139 | 152 | 271 | 483 | 504 | 745 | 2523 |
| **V004 two deletions** | **31** | **38** | **46** | **54** | **62** | **72** | **81** | **114** | **138** | **151** | **270** | **481** | **503** | **743** | **2521** |
| best known (DS1.18, computer) | 28 | 36 | 41 | 50 | 59 | 68 | 77 | 109 | 132 | 145 | | | | | |

## What the next improvement would take (updated after V004)

The three routes of the first report are superseded: V002 *is* the AKS/Shearer route, formalised
in its discrete (degree-sequence) form, which needs no real analysis. The elementary
degree/pair/cherry family that sessions 2–3 found exhausted at `(k²+3)/2` is subsumed by it.
What remains, in decreasing order of value and increasing order of cost:

1. **The constant.** `R(3,k) ≤ (1+o(1)) k²/log k` (Shearer) is the best known upper bound; the
   lower bound is `(1/2 + o(1)) k²/log k` (Hefty–Horn–King–Pfender 2025, arXiv 2510.19718).
   Improving the constant `1` is an open research problem; nothing here is likely to be cheap.

2. **Second-order refinements of the deletion argument.** The extremal configuration for V003
   is `D`-regular with `n ≈ D²/log D` vertices and all codegrees `|N(u) ∩ N(v)| ≈ log D`
   (as equal as possible); in it the secant (Jensen) step of V003 is tight. The two-level
   deletion is now V004 (in the `n, D`-only form; it equals the full two-level bound in the
   regular case). A **third level** (the same construction once more inside `G - N[v] - N[v']`,
   with the worst case taken jointly over the degree of `v` and the inner graph's max degree
   `D` or `D - 1`) was quantified exactly and **gains nothing**: at every `k ≤ 100` tested it
   returns the V003 value, because the second Cauchy–Schwarz step and the loss of a full closed
   neighbourhood at the inner level cost more than the extra `+1`. A third level could only
   help with the exact codegree structure of the inner graph, i.e. the pair sums (second
   moments of codegrees, `Σ_{uv ∈ E} d_u d_v` cross terms) that V004 avoided. Using `c_{uv} ≥ 1`
   for vertices of degree `D` is subsumed by the secant/Jensen step (it is the same
   information). All of these are `O(log k)` in `n`; the constant `1` in `k²/log k` is
   untouched. The V004 candidate set `V - 3 … V - 1` is complete up to at least `k = 400`
   (the two-level gain there is at most `3`).

3. **Small `k`.** The slack of V003/V004 is small but real: at `n = 30, D = 7` the one-level
   bound gives `α ≥ 6.856` (need `> 7`); at `n = 45, D = 9`: `8.93` (need `> 9`). Parity of the
   regular case (`nD` odd at `k = 10`) buys only `≈ 0.01`, and a case analysis on the vertices
   of degree `D - 1` at `k = 10, n = 45` leaves the case of a single such vertex open (`8.99`).
   The best known values for `k = 10..20` (`41, 50, 59, 68, 77, 87, 97, 109, 120, 132, 145`,
   DS1.18) all rest on computer searches (Angeltveit; Goedgebeur–Radziszowski; Lesser;
   Backelin), none reproducible here. `R(3,7) ≤ 24` (from V003's `25`) is out of reach of this family: even a two-level
   deletion on the `6`-regular graph on `24` vertices gives `α(W_v) ≈ 4.98 < 6`; the known
   proof goes through the Radziszowski–Kreher inequality `13α ≥ 6n - e` for triangle-free
   graphs (Ars Combin. 31, 1991), a long structural argument.

4. **What would propagate.** Unlike the V001 recursion, the Shearer-type bounds at `k` do not
   depend on the bound at `k - 1`, so a point improvement at one `k` no longer propagates; only
   an improvement of the inequality itself (routes 1–2) improves infinitely many `k`.

## What the next improvement would take (first report, before V002)

Three routes, in increasing order of cost.

1. **A saving of two in the recursion.** With `N = M + N' - 2` the degree argument above leaves
   one unit of slack: every vertex has red degree `M-2` or `M-1`, and the handshake lemma only
   constrains the parity of the number `a` of vertices of the larger degree (`a` even when `M`
   is even, `N - a` even when `M` is odd). Turning that into a contradiction is the
   Graver–Yackel / Walker style of argument used to compute the small values, and needs real
   structural work on the extremal graph; it would buy a further `~k/2` overall.

2. **A common-neighbour count.** For two *blue*-adjacent `u, v`, their common blue neighbourhood
   contains no red triangle and no blue `K_{k-2}`, so if `M'` forces `(3, k-2)` then
   `N ≤ M' + 1 + d_u + d_v - c` where `c = |N_red(u) ∩ N_red(v)|`. Double counting gives an
   average `c` of `(k-1)(k-2)/(N-k) ≈ 2` in the tight case, so *some* blue pair has `c ≥ 2`,
   which saves one more unit per two steps and would bring the record to about `k(k-1)/2`.
   The obstacle is purely formalisation cost: it needs a double count of cherries over
   `Finset` pairs and an averaging argument, well beyond what fits in one sitting, though
   comfortably inside the computation budget since none of it is evaluation.

3. **AKS / Shearer.** Anything of the form `c·k²/log k` needs the independence-number bound for
   triangle-free graphs (`α ≥ (1+o(1)) n log d / d` at average degree `d`). Shearer's proof is a
   short analytic induction on the function `f(d) = (d log d - d + 1)/(d-1)²`, but it is stated
   over the reals and would need real-analysis plumbing plus a careful ℕ-valued wrapper for the
   record (see the `Rat`/`decide +kernel` trap in `docs/CONTRIBUTING.md`). This is the only
   route to an asymptotically better record.

A point patch at a single `k` from a known exact value is *not* available here: the known values
`R(3,6) = 18`, `R(3,7) = 23`, … all rest on exhaustive generation of triangle-free graphs, which
the computation budget rules out. Proving `R(3,6) ≤ 18` by hand is possible (Kéry 1964) but it
would improve only `k = 6` and `k = 7` — downstream the parity of the chain flips and the gain
is lost from `k = 8` on.

## Problems hit

- `ForcesOn` opens with strict-implicit binders `{V} [Fintype V] [DecidableEq V]`. An
  unascribed `have h := …` instantiates them into metavariables and typeclass search gets stuck
  (the same trap the problem's own `Def.lean` documents). Every intermediate `ForcesOn` fact has
  to be ascribed, and — less obviously — applying `forcesOn_step` at `s = 2` leaves the clique
  size as `2 + 1` rather than `3`, which the unifier will not reconcile *through* the unfolded
  `ForcesOn`; the goal has to be put in the `2 + 1` form with `show` first.
- The natural-division closed form `(k² + 3)/2` exceeds the seed at `k = 0, 1`, where `f` is
  pinned to `0`. Upper records need no `pin`, but `improves` is quantified over every `k`, so
  `minWith` with the previous record is what makes the obligation go through.


## Problems hit (this session, V002–V004)

- **`ForcesOn` facts must be ascribed**, as the first report warned, and more than that: even a
  fully explicit application `forcesOn_foldl D fb hD hfb l init hfb` gets stuck on
  `DecidableEq ?m` when used with `exact`/`refine`. What works is a partial application with
  its `∀`-type written out (`have t1 : ∀ l init, ForcesOn init 3 (D+1) → ForcesOn (…) 3 (D+1)
  := forcesOn_foldl D fb hD hfb`), then instantiation, then `exact` against a goal put in the
  *syntactic* form of the fold (`show … (cand (D + 1 - 1) …)` and
  `simp only [Nat.add_sub_cancel]`); `rw [e]` with an equation `e : v (D+1) = fold…` produced
  a goal that still did not match.
- **`set` abbreviations defeat `ring`/`linarith`** (the abbreviation is an opaque atom), and
  `ring_nf` rewrites `r + 1` into `1 + r` *inside* `shearer (r + 1)`, breaking every later
  match. All arithmetic was moved into lemmas over plain variables (`cand_arith`,
  `check_arith`, `q_mono`, `sigma_le`), applied with explicit arguments.
- **`omega`/`linarith` with a huge hypothesis in context** (the ℕ certificate inequality of
  V004, a polynomial with a dozen `shearer` terms) cost 145000 heartbeats in one declaration.
  The graph argument was moved to a lemma that never sees the certificate; the whole file then
  needs 68000.
- `Finset.exists_le_of_sum_le` is the averaging tool; `sq_sum_le_card_mul_sum_sq` is
  Cauchy–Schwarz; `Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow` is double
  counting; `push_neg` is deprecated in this Mathlib (`not_or.mp`/`not_exists.mp` instead).
- The V004 record only tries the candidates `V - 3, V - 2, V - 1`; the two-level gain is at most
  `2` for `k ≤ 100`, but it grows slowly with `k`, so for large `k` (outside the fuel range) a
  later version could extend the candidate list. This is not an improvement at any `k ≤ 100`.

## Session 2 — baseline claude-opus-5 (no new version accepted)

No version was accepted in this session. The record stays at **V001, `(k²+3)/2`**. What was
established is a *negative* result that corrects route 2 of the list above, so it is recorded
here to save the next submitter the same detour.

### Route 2 (common-neighbour / cherry counting) cannot improve `(k²+3)/2`

Write `g(k) = (k²+3)/2` for the V001 bound and suppose `G` is triangle-free on `n` vertices with
no independent set of size `k+1`. Three facts are available at once:

1. **Degree above.** `N(v)` is independent, so `d(v) ≤ k`.
2. **Degree below.** `V ∖ ({v} ∪ N(v))` is triangle-free with no independent `k`-set, so
   `n - 1 - d(v) ≤ g(k) - 1`, i.e. `d(v) ≥ n - g(k)`.
3. **Pair bound.** For `u, w` non-adjacent, `V ∖ ({u,w} ∪ N(u) ∪ N(w))` is triangle-free with no
   independent `(k-1)`-set, so with `c = |N(u) ∩ N(w)|`,
   `n ≤ 2 + d(u) + d(w) - c + g(k-1) - 1`, i.e. `c ≤ d(u) + d(w) + g(k-1) + 1 - n`.

Because `G` is triangle-free, adjacent pairs have `c = 0`, so the cherry identity is
`Σ_v C(d(v),2) = Σ_{u,w non-adjacent} c`. Feeding 3 into the right-hand side and 1–2 into the
left gives the only inequality this method can produce; a contradiction needs
`d(d-1) > (2d + g(k-1) + 1 - n)(n - 1 - d)` for every degree `d` in the admissible window.

Evaluated over `k = 3 … 13`, the smallest `n` that this kills is **exactly `g(k+1)`** at every
odd `k`, and *no* `n` at all at every even `k`. In other words the cherry count reproduces the
parity-refined recursion and buys nothing beyond it.

The reason is visible in the tight case. At `n = g(k) + k` with `k` even, 1 and 2 force `G` to
be exactly `k`-regular, and then the average of `c` over non-adjacent pairs is
`k(k-1)/(g(k)-1) = 2 - 2/k < 2`, while the pair bound allows `c ≤ 2`. The count is consistent to
the last unit: for every `v`, exactly `k` vertices have `|N(u) ∩ N(v)| = 1` and exactly
`g(k) - 1 - k` have `2`. Nothing is over-counted, so no contradiction exists at this level of
resolution — the earlier report's estimate that "some blue pair has `c ≥ 2`" is right but yields
equality, not a saving.

### Why a saving of one at a single `k` is worthless here

Improving `g` by `1` at one `k` does **not** propagate: the parity refinement fires when `k+1`
and `g(k)` are both even, so shifting `g(k)` by an odd amount moves the saving to the other half
of the steps and the gain is cancelled at the next step but one. Only an **even** saving at some
`k` propagates to every larger `k`. Concretely, `R(3,6) ≤ 18` (Kéry) would give `R(3,7) ≤ 25`
against V001's `26` and then `R(3,8) ≤ 33`, equal to V001 — one value improved, then nothing.
The first useful point target is therefore `R(3,7) ≤ 24` (truth `23`, V001 gives `26`), which
would shift the whole tail down by `2`.

`R(3,7) ≤ 24` was attempted and abandoned. The elementary constraints do come out strong: with
`n = 24`, `α ≤ 6` the degrees lie in `{5,6}`, any two vertices in a common neighbourhood have
`c ≥ 1` and hence degree sum `≥ 9`, so **every vertex has at most one neighbour of degree 5**,
which bounds the number of degree-5 vertices by `n/5`. But the residual `6`-regular case
survives every count tried, exactly as in the general argument above. The same happens for
`R(3,6) ≤ 18`: the constraints force at most four degree-4 vertices, and the 5-regular case on
18 vertices is numerically consistent with all of 1–3.

### Conclusion for the next submitter

Everything reachable from the local degree/pair/cherry counts is already in V001; that family of
arguments is now known to be exhausted. The two live routes are the ones the first report listed
as expensive, and there is no cheap third one:

- **Structural elimination of the regular extremal case** (Graver–Yackel / Walker). At `n = g(k)
  + k`, `k` even, the counterexample must be `k`-regular, triangle-free, with `α = k` exactly,
  and every non-neighbourhood an extremal `(3,k)` graph. Ruling that out — even for one even
  `k` — saves `1` there and `2` in total after the parity flip, and propagates.
- **AKS / Shearer**, the only asymptotic route.

## Session 3 — baseline claude-opus-5 (no new version accepted)

The record stays at **V001, `(k²+3)/2`**. Two things were established; both are negative, and
both are recorded here so that the next submitter does not repeat them.

### The tight configuration is exactly determined, and the local counts are *consistent to the unit*

Session 2 reported that the cherry count "reproduces the parity recursion". This session pinned
down why, in a form that is usable. Write `m = k - 1` and suppose, for odd `k` (the steps where
the V001 parity saving does **not** fire), that a counterexample `G` to
`R(3,k) ≤ b(k-1) + k - 2` exists, i.e. `G` is triangle-free on `n = b(k-1) + k - 1` vertices
with `α(G) ≤ k - 1`. For odd `k`, `m` is even and `b(k-1) = m²/2 + 1`, so `n = m²/2 + m + 1`.

Then all of the following hold simultaneously, and **none of them conflicts**:

1. `G` is `m`-regular (degrees are `≤ m` because neighbourhoods are independent, and `≥ m`
   because `n - 1 - d(v) ≤ b(k-1) - 1`).
2. Every `N(v)` is therefore a *maximum* independent set, so every `u ∉ N[v]` has at least one
   neighbour in `N(v)`: `c_{uv} = |N(u) ∩ N(v)| ≥ 1`.
3. The pair bound gives `c_{uv} ≤ d(u) + d(v) + b(k-2) + 1 - n = k + b(k-2) - b(k-1) = 2`,
   using `b(k-1) - b(k-2) = k - 2` at odd `k`. So **`c_{uv} ∈ {1, 2}` for every non-adjacent
   pair**.
4. Locally at `v`: `Σ_{u ∉ N[v]} c_{uv} = m(m-1)` spread over `n - k = m²/2` vertices, so
   exactly `m` of them have `c = 1` and `m²/2 - m` have `c = 2`.
5. Globally: 4 forces `m²/2 · n / 2` cherry-pairs in total, and the number of non-adjacent pairs
   is `n(n-1-m)/2`. Equating the two gives `2(n - 1 - m) = m²`, i.e. `n = m²/2 + m + 1` —
   **the value we started from**, identically.

So the counting closes on itself. The hypothetical extremal graph is a *near-Moore* graph:
`m`-regular, triangle-free, on `m²/2 + m + 1` vertices, with every non-adjacent pair having one
or two common neighbours (a Moore graph of girth 5 would be `m²+1` vertices with `c ≡ 1`). And
it genuinely **exists** for `m = 2` (`C₅`, giving `R(3,3) = 6`) and `m = 4` (the cyclic graph
`C₁₃(1,5)`, giving `R(3,5) = 14`). It must *not* exist for `m = 6` (`n = 25`, while
`R(3,7) = 23`), but since it exists for the two smallest cases there is **no uniform
counting/parity argument** that kills it — the obstruction at `m = 6` is arithmetic in `m`, not
structural in the counts. Any further saving therefore needs an eigenvalue or design-theoretic
argument on this near-Moore configuration, or the AKS/Shearer route.

### The below-`nMin` slack is not exploitable

V001's record reports `1` at `k = 1`, while `f 1 = 0` (pinned). Replacing it by `0` is sound and
its `valid`/`improves` obligations are one line each, but `StrictlyImprovesUpper` requires the
witness `n₀` to satisfy `n₀ ≥ nMin = 2`, so `k = 1` cannot be a witness. The scaffold written for
this was removed. **There is no free improvement below `nMin`** — the obligation shape forbids
it, which is the right design.

### Conclusion, unchanged from session 2 but now sharper

- The degree/pair/cherry family of arguments is **provably exhausted** at this record: its
  counts are exactly consistent with the V001 bound (item 5 above).
- The next saving must rule out the near-Moore configuration `(m`-regular, triangle-free,
  `m²/2 + m + 1` vertices, `c ∈ {1,2})` for even `m ≥ 6`. Doing so at one `m` saves `1` there and
  `2` for every larger `k` after the parity flip.
- **AKS / Shearer** remains the only asymptotic route.
