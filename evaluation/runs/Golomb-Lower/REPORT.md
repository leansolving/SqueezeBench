# Golomb — lower bound track

`f m` = the least length of an `m`-mark Golomb ruler (a Sidon set of size `m` in `[0, L]`
with a mark at `L`), OEIS A003022, `nMin = 1`.

## Literature

* **Trivial counting bound.** The `C(m,2)` positive differences are distinct and lie in
  `[1, L]`, so `f m ≥ m(m−1)/2`. This is the seeded record V000.
* **Erdős–Turán / Lindström.** A Sidon set in `[1, N]` has at most
  `N^{1/2} + N^{1/4} + 1` elements (P. Erdős, P. Turán, *On a problem of Sidon in additive
  number theory*, J. London Math. Soc. 16 (1941) 212–215; B. Lindström, *An inequality for
  B₂-sequences*, J. Combin. Theory 6 (1969) 211–212). Inverting gives
  `f m ≥ m² − 2m^{3/2} + O(m)`; this is still the best general lower bound known, up to
  lower-order terms. Small refinements of the constant in the `m^{5/4}` term are due to
  Cilleruelo, Ruzsa and Vinuesa.
* **Exact values** are known only by exhaustive search, through `m = 28`
  (`G(27) = 553`, distributed.net OGR-27, 2014; `G(28) = 585`, OGR-28, 2022). They are
  *reporting only* here: reproducing them in Lean means redoing the search, which the
  computation budget forbids. Consequently no patch at a single small `m` is available to
  this track.
* Asymptotically `f m = m² − 2m^{3/2} + O(m^{5/4})` is not known to be improvable; the
  upper side (best known rulers) sits around `m²` with a smaller second-order term, so a
  large gap remains at every `m` and is not a formalisation artefact.

Added by trial claude-opus-5.5:

* **Lindström's sum argument** (B. Lindström, J. Combin. Theory 6 (1969) 211–212): the
  `M = ∑_{j≤t}(m−j)` differences of order `≤ t` are distinct, so their sum `≥ M(M+1)/2`, while it
  telescopes to `≤ t(t+1)/2 · L` minus end terms. Same leading terms as Erdős–Turán; the basis
  of V006–V008.
* **Explicit all-`m` closed forms**: A. Dimitromanolakis (thesis, Univ. of Toronto, 2002,
  Thm 4.9) `G(m) > m² − 2m^{3/2} + √m − 2`; K. O'Bryant (*On the size of finite Sidon sets*,
  2022) `G(m) ≥ m² − 2m^{3/2} + m + √m − 1`. Both are below V006 already (e.g. `m = 100`:
  8008 and 8109 against 8148).
* **Improved second-order constant**: Balogh–Füredi–Roy (Amer. Math. Monthly 130 (2023)
  437–445), O'Bryant (2022) `G(m) ≥ m² − 1.99405 m^{3/2}` for large `m`, Carter–Hunter–O'Bryant
  (2023) `m² − 1.96365 m^{3/2} − O(m)` (computer-assisted). Asymptotic statements, not
  directly usable at moderate `m` (reported by a GPT-6 Astra consultation; not checked in
  detail).
* **LP relaxation** (Lorentzen–Nilsen 1991; Hansen–Jaumard–Meyer, Discrete Appl. Math. 94
  (1999) 205–225; Shearer, Electron. J. Combin. 6 (1999) R31; Meyer–Jaumard, Discrete Appl.
  Math. 154 (2006) 120–144): `∑_{E} d ≥ |E|(|E|+1)/2` for every set `E` of pairs. Solved
  numerically here by cutting planes (scratch only): `m = 12: 81.29`, `20: 257.5`,
  `27: 499.84`, `30: 629.74`, `40: 1175.71`, `50: 1899.43`, `60: ≥ 2802.2` — above every record
  so far; V008 formalises most of it (see below).

## V001 — baseline claude-opus-5

**Bound.** With `q = ⌊√m⌋` (at least 1), `v = q m − q(q+1)/2` and `u = v + 1`,

```
record m = max ( m(m−1)/2 ,  (2 q u m − v (v+1)) / (q (q+1)) − u )
```

i.e. roughly `m² − 2 m^{3/2} + O(m)`, against the seed's `m²/2`.

**Idea.** Slide a window of length `u = v + 1` over `[0, L]` and let `cnt s` be the number
of marks in the window ending at `s`. Over the `L + v + 1` windows that can meet a mark:

* `∑ cnt s = m (v+1)`, since every mark lies in exactly `v + 1` of them;
* `∑ cnt s (cnt s − 1) ≤ v (v+1)`: two marks at distance `d` share `v + 1 − d` windows, and
  the Sidon property makes the distances distinct, so the total is at most
  `2 ∑_{d=1}^{v} (v+1−d)`;
* for every natural `n` and `q`, `2 q n ≤ n (n−1) + q (q+1)`, the secant of the convex
  `n(n−1)` through the two integer points `n = q, q+1`; it is `(n−q)(n−q−1) ≥ 0`.

Summing the third over the windows and inserting the first two gives the **master
inequality**

```
2 q u m ≤ (L + u) q (q+1) + (u−1) u        for every q, u
```

which solves for `L`. Because the secant exploits the integrality of `cnt s`, this is a
little *stronger* than the Cauchy–Schwarz (Jensen) step of the classical Erdős–Turán proof,
which is the `q → real` limit of the same estimate.

**Why this choice.** It is the only route to the `m²` leading constant; the seed's `m²/2`
is exactly what a block (non-sliding) partition gives, and no patch at a single `m` is
reachable without an exhaustive search. Fixed-`q` variants degrade to `q/(q+1) · m²`, so
`q ≈ √m` is forced.

**Witness.** `n₀ = 11`: `55 → 63` (the true value is `72`).

**Cost.** 16828 heartbeats in all (limit 200000). `Nat.sqrt` is defined by well-founded
recursion and does not reduce in the kernel, so `Def.lean` carries `isqrt`, a Newton
iteration with structural fuel.

## V002 — baseline claude-opus-5

**Bound.** `bnd m q u = (2 q u m − (u−1) u) / (q (q+1)) − u` is V001's master inequality
solved for `L`, and it is valid for *every* pair `(q, u)`. V002 is

```
record m = max ( V001.record m , max over 12 pairs (q, u) of bnd m q u )
```

with `q ∈ {⌊√m⌋−1, …, ⌊√m⌋+2}` and, for each `q`, `u ∈ {u₀, u₀+1, u₀+2}` where
`u₀ = q m − q(q+1)/2`. For fixed `q` the right-hand side is a downward parabola in `u`
whose real maximiser is `q m − (q²+q−1)/2`, so the integer optimum is one of those three;
and the optimal `q` is one of the four integers around `⌊√m⌋`. Over `1 ≤ m ≤ 200` this
maximum equals the exact integer optimum of the master inequality at every `m`.

**Idea.** No new mathematics — `V001.master` is reused verbatim; the gain is that V001
committed to a single `(q, u)`.

**Why this choice.** It improves at a positive fraction of all `m` (106 of the first 399,
in bands just above each square: `9, 10, 16–18, 25–27, 36–39, 49–51, …`),
so at infinitely many `n`, and costs almost nothing in budget. The next real gain needs a
new estimate, not a better parameter (see below).

**Witness.** `n₀ = 9`: `38 → 40` (the true value is `44`).

**Cost.** 2743 heartbeats in all; `V001.master` and `V001.div_le_of_mul_le` are imported and
reused unchanged, so the only new proof is `bnd_le`.

## V003 — baseline claude-opus-5

**Bound.** With `A = K(K+1)/2` the boundary block length and
`G = K(K+1)·(q−K)(q−K+1) = 2A(q−K)(q−K+1)` the boundary gain,

```
gbnd m q u K = (2 q u m + G − (u−1) u) / (q (q+1)) − u      [guarded, see below]
record m = max ( V002.record m , max over 27 triples (q, u, K) of gbnd m q u K )
```

with `q ∈ {⌊√m⌋−1, ⌊√m⌋, ⌊√m⌋+1}`, for each `q` the three `u` around V002's maximiser, and
`K ∈ {⌊q/2⌋−1, ⌊q/2⌋, ⌊q/2⌋+1}`. Roughly `m² − 2m^{3/2} + (1.3 + 1/16) m`.

**Idea.** The **boundary effect** announced by V002 as the next step, in its cheapest
form. In V001's sliding window over `s ∈ [0, L+u−1]`, the window ending at `s` meets only
`[0, s]`, and the pairwise distances of the marks it holds are *distinct* elements of
`[1, s]`, so `C(cnt s, 2) ≤ s`; symmetrically `C(cnt s, 2) ≤ L + u − 1 − s`, because the
window meets only `[s−u+1, L]`. Hence `cnt s ≤ K` on the first and last
`A = K(K+1)/2` windows, as `2A = K(K+1)` is exactly the pair budget of `K` marks. On such a
window the integrality (tangent) step of the master inequality is slack by
`(q − cnt s)(q − cnt s + 1) ≥ (q − K)(q − K + 1)`, and the `2A` boundary windows therefore
add `G` to the right-hand side:

```
2 q u m + 2 A (q−K)(q−K+1) ≤ (L + u) q (q+1) + (u−1) u.
```

Maximising `A (q−K)² ≈ (K²/2)(q−K)²` over `K` gives `K ≈ q/2` and `G ≈ q⁴/16 ≈ m²/16`,
i.e. about `m/16` on the bound. Two side conditions: the two blocks must be disjoint,
`2A ≤ L`, which is guarded by `2A ≤ V002.bnd m q u` — that value is already known to be at
most `L`, so the guard is checkable from `m` alone; and `q, u ≥ 1`, also guarded. The guard
returns `0` when it fails, so `gbnd` is a lower bound for every parameter triple.

**Why this choice.** It improves the record at **390 of the first 399 values of `m`** (all
but nine small ones), so at infinitely many `n`, and it is a new constraint rather than a
reparametrisation — V002 had exhausted the old linear program.

**Witness.** `n₀ = 8`: `30 → 31` (the true value is `34`).

**Cost.** 25611 heartbeats in all (limit 200000); heaviest `master'` 10304 and `tangent'`
7805. `win`, `cnt`, `sum_cnt`, `sum_choose_eq`, `sum_spread_le`, `spread_injOn`, `tangent`,
`two_choose_two`, `div_le_of_mul_le` are V001's, `spread`/`exists_pair` V000's, `bnd`/`bnd_le`
V002's.

## V004 — baseline claude-opus-5

**Bound.** Two nested boundary blocks. With `slack q K = (q−K)(q−K+1)`,
`A_i = K_i(K_i+1)/2`, `W₁ = slack q K₁ − slack q K₂` and `W₂ = slack q K₂`,

```
gain q K₁ K₂ = 2 (A₁ W₁ + A₂ W₂)
gbnd m q u K₁ K₂ = (2 q u m + gain q K₁ K₂ − (u−1) u) / (q (q+1)) − u   [guarded]
record m = max ( V003.record m , max over 24 tuples (q, u, K₁, K₂) of gbnd … )
```

with `q ∈ {⌊√m⌋−1, ⌊√m⌋, ⌊√m⌋+1}`, `u ∈ {u₀+1, u₀+2}`, `K₁ ∈ {⌊q/3⌋, ⌊q/3⌋+1}`,
`K₂ ∈ {⌊3q/5⌋, ⌊3q/5⌋+1}`; the guard adds `K₁ < K₂` to V003's. Roughly
`m² − 2m^{3/2} + (1.3 + 1/18) m`.

**Idea.** V003's boundary slack is a *step function* with one step: it credits every one of
the first `A` windows with the slack of a window holding `K` marks, although the very first
windows hold far fewer. The true profile is `slack q κ(s)` with `κ(s) ≈ √(2s)` the local
Sidon cap, whose integral is `q⁴/12` per end against V003's `q⁴/32`. V004 is the two-step
Riemann sum: on the inner block `s < A₁` the window holds at most `K₁` marks and is credited
`W₁ + W₂ = slack q K₁`; on `A₁ ≤ s < A₂` it holds at most `K₂` and is credited
`W₂ = slack q K₂`. The telescoping weights make each credit exactly the slack available, so
the per-window obligation `∑_{j : s < A_j} W_j ≤ (q − cnt s)(q − cnt s + 1)` holds with
equality at the innermost block containing `s`. `master2` states it for arbitrary
`A₁ ≤ A₂`, `K₁ < K₂`, `W₁`, `W₂` under exactly those two inequalities, so a later version
can reuse it.

**Why this choice.** It improves at **380 of the first 399 `m`**, i.e. at infinitely many
`n`, it uses the same proof skeleton as V003 (five window cases instead of three, four
indicator sums instead of two), and it captures a further `q⁴/18 − q⁴/32` of the boundary
slack, about `m/18` on the bound.

**Witness.** `n₀ = 12`: `78 → 79`.

**Cost.** 24063 heartbeats in all; heaviest `master2` 16192.

## V005 — baseline claude-opus-5

**Bound.** V004 with a **third** nested block: caps `K₁ < K₂ < K₃` around `q/4`, `q/2`,
`7q/10`, blocks `A_i = K_i(K_i+1)/2`, weights `W_i = slack q K_i − slack q K_{i+1}`
(`W₃ = slack q K₃`), gain `2 (A₁W₁ + A₂W₂ + A₃W₃)`, and

```
record m = max ( V004.record m , max over 10 tuples (q, u, K₁, K₂, K₃) of gbnd … )
```

**Idea.** The next term of the same Riemann sum; `master3` is `master2` with one more
window case (`A₂ ≤ s < A₃` and its mirror) and two more indicator sums, and states the
inequality for arbitrary `A₁ ≤ A₂ ≤ A₃`, `K₁ < K₂ < K₃` under the three partial-sum
conditions `W₁+W₂+W₃ ≤ slack q K₁`, `W₂+W₃ ≤ slack q K₂`, `W₃ ≤ slack q K₃`.

**Why this choice.** Improves at **275 of the first 299 `m`**, i.e. at infinitely many `n`,
by a further `≈ q⁴/18 → q⁴/15` of the boundary slack. It is the cheapest remaining step,
and it shows the pattern is uniform in the number of blocks.

**Witness.** `n₀ = 18`: `197 → 198`.

**Cost.** 39170 heartbeats in all; heaviest `master3` 30594. Note the growth:
`master'` 10304 (1 block), `master2` 16192 (2), `master3` 30594 (3) — the window case
analysis roughly doubles the cost of the heaviest declaration every two blocks, so about
`J = 5` is where the 200000-heartbeat ceiling starts to matter if the proof is written this
way.

## V006 — trial claude-opus-5.5

**Bound.** Lindström's argument with a boundary correction, bootstrapped. With
`M = t m − t(t+1)/2`, `G j = g 1 + … + g j` for a valid lower bound `g`,

```
lind g m t = ⌈ (M (M + 1) + 4 ∑_{j=1}^{t} G j) / (t (t + 1)) ⌉        (0 < t < m)
record m   = max (V005.record m) (max over t ∈ {⌊√m⌋−1, ⌊√m⌋} of lind (record) m t)
```

where `g` is the record itself at the arguments `≤ t` (structural fuel, `core`).

**Idea.** Sort the marks `a₀ < … < a_{m−1}`. The `M` differences of order `≤ t` are distinct
positive integers, so they sum to at least `M(M+1)/2`; the order-`j` ones telescope to
`∑_{r<j} (a_{m−j+r} − a_r) ≤ jL − 2 G j`, because the first (last) `r + 1` marks form a ruler
of length `≤ a_r` (`≤ L − a_{m−1−r}`), hence `≥ f(r+1) ≥ g(r+1)`. A new argument, not a
reparametrisation of the window count: the window LP of V001–V005 was exhausted, and
Lindström's sum with the prefix/suffix sub-ruler bounds is `Θ(m)` better.

**Why this choice.** It improves V005 at 394 of the first 400 `m` (all but 1–5 and 8), by
an amount growing linearly in `m`, with a short proof (23019 heartbeats in all).

**Witness.** `n₀ = 100`: `8143 → 8148`.

## V007 — trial claude-opus-5.5

**Bound.** A *separated family* is a set of `k` index intervals of `n` consecutive marks
each, any two sharing at most one mark. `H fuel k n` bounds its total span:

```
H 0 k n     = k · V006.record n
H (f+1) k n = max (k · V006.record n) (max over u ∈ {⌊√n⌋−2,…,⌊√n⌋+1} of
              ⌈ (Q(Q+1) + 2 ∑_{o=1}^{u} ∑_{r=1}^{o−1} H f (2k) (r+1)) / (u(u+1)) ⌉)
              with Q = k (u n − u(u+1)/2), when 0 < u < n, 2u ≤ n + 1
record m    = H m 1 m
```

**Idea.** In V006 the boundary term `b_r = a_r + (L − a_{m−1−r})` was bounded by
`2 f(r+1) ≈ 2r²`. The first and last `r + 1` marks share no pair, so all their differences
are distinct *jointly* and Lindström's argument on the two pieces together gives
`b_r ≳ 4r²`. Recursively, the `2k` end pieces of a separated family form a separated family
(`2r ≤ n − 1`), so one lemma (`family_master`) with an induction on the fuel covers all
levels. The two-end observation came from a GPT-6 Astra consultation; the family form is ours.

**Why this choice.** Improves V006 at 394 of the first 400 `m` (all but 1–4, 6, 7), with a
gain growing linearly (`+4` at 27, `+17` at 100, `+80` at 400), and it makes `m = 5` exact
(`11`). 30224 heartbeats in all.

**Witness.** `n₀ = 100`: `8148 → 8165`.

## V008 — trial claude-opus-5.5

**Bound.** A certificate checker for Lindström-type inequalities on the sets
`E(u, s)` = pairs of order `≤ u` ∪ all pairs inside the first `s` or last `s` marks. With
`L' = a_{m−1} − a₀` and `b_r = (a_r − a₀) + (a_{m−1} − a_{m−1−r})`,

```
n (n+1) + 2 ∑_r neg(u,s,r) b_r ≤ u(u+1) L' + 2 ∑_r pos(u,s,r) b_r,
n = M_u + (s−1−u)(s−u),  neg = (u−r) + (s−1−u−r),  pos = [r<s](r−u).
```

A weighted list of triples `(λ, u, s)` with net coefficients `POS_r ≤ NEG_r` gives
`L ≥ ⌈(∑λ n(n+1) + 2∑_r (NEG_r−POS_r)·H _ 2 (r+1)) / ∑λ u(u+1)⌉` (V007's `H` bounds `b_r`).
The record builds the chain `s_j = s₀ + j`, `u_j = 1 + ⌊j(s₀+J−3)/J⌋`, `λ_j = (J+1)² − j²`,
repairs it top-down with plain Lindström sets, checks it, and tries six `(s₀, J)` around
`(3⌊√m⌋/4, 5⌊√m⌋/4 − 5)`.

**Idea.** The subset-sum LP relaxation (`∑_E d ≥ |E|(|E|+1)/2` for every pair set `E`), solved
numerically by cutting planes, is far above V007, and its optimal duals are nested sets
"order `≤ u` plus the pairs inside the dense end pieces", mixed over many `u` with smoothly
decreasing weights. For the sets `E(u, s)` the sum of differences is linear in `L'` and the
`b_r`, so the restricted LP is small; the chain above nearly attains it (`m = 100`: 8210 vs
LP 8214.0). The gain over V007 grows like `m^{3/2}` (`≈ 0.05–0.06 m^{3/2}` for
`100 ≤ m ≤ 1600`), i.e. it improves the constant 2 of the `m^{3/2}` term in this range.

**Why this choice.** The largest gain available among everything examined, at almost all `m`
(every `m` in 16–150 except 32–35, 381 of the first 400), provable with one identity
(`ext_id`, induction on `s`) plus a sound checker, 68318 heartbeats in all.

**Witness.** `n₀ = 100`: `8165 → 8210`.

## Values

| m | 1 | 4 | 5 | 9 | 11 | 27 | 28 | 50 | 100 | 200 |
|---|---|---|---|---|---|---|---|---|---|---|
| V000 (start) | 0 | 6 | 10 | 36 | 55 | 351 | 378 | 1225 | 4950 | 19900 |
| V001 | 0 | 6 | 10 | 38 | 63 | 484 | 525 | 1857 | 8127 | 34598 |
| V002 | 0 | 6 | 10 | 40 | 63 | 485 | 525 | 1860 | 8132 | 34602 |
| V003 | 0 | 6 | 10 | 40 | 64 | 486 | 527 | 1863 | 8138 | 34615 |
| V004 | 0 | 6 | 10 | 40 | 64 | 487 | 528 | 1864 | 8141 | 34620 |
| V005 | 0 | 6 | 10 | 40 | 64 | 488 | 529 | 1865 | 8143 | 34624 |
| V006 | 0 | 6 | 10 | 41 | 65 | 489 | 530 | 1867 | 8148 | 34639 |
| V007 | 0 | 6 | 11 | 42 | 66 | 493 | 534 | 1875 | 8165 | 34676 |
| V008 | 0 | 6 | 11 | 42 | 66 | 496 | 536 | 1888 | 8210 | 34820 |
| LP relaxation (numerical, not a theorem here) | | | | | | 500 | | 1900 | | |
| f (known) | 0 | 6 | 11 | 44 | 72 | 553 | 585 | ? | ? | ? |

## What the next improvement would take

**More boundary blocks, `J = 4, 5, …`.** V003/V004/V005 are the `J = 1, 2, 3` Riemann sums
of the boundary slack profile `slack q κ(s)`, `κ(s) ≈ √(2s)`; its exact integral is `q⁴/12`
per end, i.e. `m/6` on the bound, against `q⁴/32`, `≈ q⁴/18`, `≈ q⁴/15`. The pattern
generalises mechanically: blocks `A₁ ≤ … ≤ A_J` with caps `K₁ < … < K_J`, telescoping
weights `W_j = slack q K_j − slack q K_{j+1}`, and the per-window obligation
`∑_{j : s < A_j} W_j ≤ slack q (cnt s)`. Each extra block costs one more case in the window
analysis and two more indicator sums. Writing the `J` blocks as a `List` and the sum as a
`Finset.sum` over it would replace the case explosion by one induction and is the way to go
past `J ≈ 5`; that is the main piece of Lean work left on this route. The remaining headroom
of the whole route is only `m/6 − m/15 ≈ 0.09 m`, however.

Beyond the boundary the old note still applies: the linear program behind the master inequality is
tight — from `∑ cnt = m u`,
`∑ cnt (cnt − 1) ≤ (u−1) u` and integrality alone, V002 already extracts the exact
optimum. Any further gain needs a *new constraint*. The natural one is the **boundary
effect**: the windows ending at `s < u` can only meet marks in `[0, s]`, and a Sidon set in
an interval of length `s` has at most about `√(2s)` marks, so those windows are far below
the average occupancy `≈ √m` that the extremal solution assumes. Summing the slack
`(cnt − q)(cnt − q − 1)` over `s ≲ m/2` at both ends is worth about `m²/6` extra on the
right of the master inequality, i.e. about `m/6` on the bound — an `O(m)` gain, the same
order as the term the Lindström refinement improves. Formalising it needs the local bound
`C(k,2) ≤ s` for `k` marks in a window of length `s`, plus a summation of
`(q − √(2s))²`, which is a genuine piece of work.

Beyond that, the `m^{5/4}`-term refinements (Lindström; Cilleruelo–Ruzsa–Vinuesa) use
Fourier or higher-moment arguments and look out of reach at this budget.

Problems hit, for the next submitter:

* `Nat.sqrt` is well-founded recursion; `decide +kernel` cannot evaluate it cheaply. Use
  V001's `isqrt` (Newton with structural fuel) or another structurally recursive version.
* Exact values of `f` may not be used: proving `f 5 = 11` in Lean is an exhaustive search
  and the computation budget forbids it. Every improvement on this track has to be a
  theorem valid for all `m`.

## Search notes added by baseline claude-opus-5 (no new version accepted in this session)

Two things were established by exhaustive numerical search over the record formulas
(script in scratch only; all values are of the *record functions*, not of `f`):

**1. V005's parameter set is already exactly optimal for three blocks.** Maximising
`V005.gbnd m q u K₁ K₂ K₃` over *all* triples `1 ≤ K₁ < K₂ < K₃ ≤ q`, with `q` and `u`
ranging over V005's own sets (`q ∈ {⌊√m⌋−1, ⌊√m⌋, ⌊√m⌋+1}`, `u ∈ {u₀+1, u₀+2}`), gives
**exactly V005's value at every `m` from 1 to 199** — 0 improvements out of 199. So the
V001→V002 trick (widen the parameter search, reuse the same `master` lemma, cheap proof)
is *not* available on top of V005: the caps `(⌊q/4⌋, ⌊q/2⌋, ⌊7q/10⌋)` and their five
neighbours already attain the three-block optimum. Widening `q` or `u` does not help either.
A prospective V006 must therefore add a genuinely new inequality, not a new parameter.

**2. What the fourth block is worth.** The natural V006 is `master4`: blocks
`A₁ ≤ A₂ ≤ A₃ ≤ A₄`, caps `K₁ < K₂ < K₃ < K₄`, telescoping weights
`W_j = slack q K_j − slack q K_{j+1}` (`W₄ = slack q K₄`), gain
`2 ∑_j blockLen K_j · W_j`, and the same guard with `2 · blockLen K₄ ≤ V002.bnd m q u`.
Exhaustive maximisation over all `K₁ < K₂ < K₃ < K₄` gives

| m | 20 | 30 | 50 | 80 | 100 |
|---|---|---|---|---|---|
| V005 (3 blocks) | 251 | 616 | 1865 | 5084 | 8143 |
| 4 blocks | 251 | 616 | **1866** | **5085** | **8144** |

so `+1` from about `m = 50` on (and at infinitely many `m` above it), nothing below —
consistent with the report's estimate that the whole boundary route has only
`m/6 − m/15 ≈ 0.09 m` of headroom left, of which the fourth block takes roughly a third of
what remains. The optimal caps sit near `(q/9, q/3, 5q/9, 7q/9)` at `m = 100` and near
`(q/6, q/3, q/2, 2q/3)` at `m = 50`; a workable fixed choice to try first is
`K_j = ⌊j q / 5⌋` for `j = 1, 2, 3, 4`, with the neighbours `+1` on each.

**Why nothing was submitted.** `master4` is a from-scratch adaptation of V005's `master3`
— one more window case at each end, two more indicator sums — and V005's own note already
measures the growth (`master'` 10304 → `master2` 16192 → `master3` 30594 heartbeats, so
`master4` lands around 55000–60000, still inside the 200000 budget). It did not fit in the
session's remaining time, and an unaccepted version is deleted, so the search results are
recorded here instead. The next submitter should go straight to `master4` with the caps
above; the `List`/`Finset.sum` refactor noted above only becomes necessary around `J = 5`.

## Next steps after V008 — trial claude-opus-5.5 (session ended, V009 not started)

**State.** V006 (Lindström + prefix/suffix sub-ruler bounds, bootstrapped), V007 (separated
families of intervals: the first and last `r+1` marks share no pair, recursively) and V008
(checked certificates of extended Lindström sets `E(u, s)`) were accepted. No `V009` directory
exists; everything below is numerical exploration in the session scratch directory under
`.lake/scratch/Golomb-Lower/` (Python scripts, run with the venv there: `model.py`/`fast.py`
reproduce V000–V006, `rec.py` V007's `H`, `chain3.py` V008's certificate, `lp.py`/`lpdual.py`
the full LP by cutting planes, `blp.py`/`bgen.py`/`bgen2.py` the LP in "b-space",
`gchain.py` the parameter search started for V009).

**The b-space view.** With `L' = a_{m−1} − a₀` and `b_r = (a_r − a₀) + (a_{m−1} − a_{m−1−r})`,
any symmetric pair set whose gap coverage is constant in the middle has
`∑_E d = κ L' + ∑_r c_r b_r`; a certificate is a nonnegative combination with all net
`c_r ≤ 0`, after which `b_r ≥ V007.H _ 2 (r+1)` finishes. V008's Lean machinery
(`ext_id`, `cert_sum`, `certBound_le_span`) is written so that new set shapes only need a new
`ext_id`-style identity and new `negC`/`posC`.

**The next gain (about +30 at m = 100).** Add to `E(u, s)` the pairs of order `u + 1` inside
the interior interval `[p, m−1−p]` (needs `p ≥ s − u − 1` so that they are not already inside
the end pieces, and `2(p+u) ≤ m − 1`). Their sum telescopes (V006's `telescope` on the
sequence shifted by `p`) to `(u+1) L' − ∑_{r=p}^{p+u} b_r`, and there are `m − 2p − u − 1` of
them; so the item inequality becomes `neg' = neg + [p ≤ r ≤ p+u]`, `L'`-coefficient
`(u+1)(u+2)` instead of `u(u+1)`, and `n' = n + (m − 2p − u − 1)`. In b-space LP with these sets
(`bgen2.py`): `m = 50: 1898.09` (full LP 1899.43), `m = 100: 8240.08`, `m = 200: 34893.41`,
against V008's 1888 / 8210 / 34820. The optimal certificates are again chains:
`s_j = s₀ + j`, `u_j` from 1 rising about one per step, `p_j` decreasing slowly
(`m = 100`: `s` 8→22, `u` 1→15, `p` 12→6; `m = 200`: `s` 11→34, `u` 1→24, `p` 15→9), with a
long tail of small weights. A first parametric search (`gchain.py`: linear `u_j` and `p_j`,
quadratic or linear weights, V008's greedy repair) reached only 1890 at `m = 50` and 8212 at
`m = 100`, so the weight profile and the `p_j` rule still need work before this is worth a
version — try reading the LP's weights at several `m` and fitting them in units of `√m`, or a
greedy/tightness rule that computes the weights. The Lean side is a modest extension of V008:
`F` gets the extra disjunct, `ext_id` one more summand, `okItem` the two conditions on `p`.

**Other directions.** (i) Improve `b_r`'s lower bound by applying V008-style certificates to
the two-end family itself (V007's `H` uses plain Lindström sets per level). (ii) `m ≤ 15`
and `32 ≤ m ≤ 35` are not improved by V008 (the six parameter candidates are poor there); the
full LP is still above the record at small `m` (e.g. `m = 20`: 257.5 against 256, `m = 12`:
81.29 against 81), so a wider parameter search or a few more candidates would give `+1`s
there. (iii) The LP gain over V007 grows like `m^{3/2}` (`≈ 0.049 m^{3/2}` at `m = 100`,
`0.062` at `m = 1600` in b-space), so these certificates improve the constant of the `m^{3/2}`
term in the tested range; whether that persists asymptotically was not established.

**Problems hit.** `pkill -f <pattern>` also matches the shell running it; kill by PID.
`#eval` of V007/V008 over hundreds of `m` is slow in the interpreter (minutes), while
`decide +kernel` at a single `m ≤ 100` is fast (≈ 8400 heartbeats for V008 at 100).
