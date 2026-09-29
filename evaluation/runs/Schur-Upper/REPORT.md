# Schur — upper bound track

`f k` = the largest `N` such that `{1, …, N}` splits into `k` sum-free parts (OEIS A045652,
sum-free including `x = y`, so `2x = z` is forbidden too). `nMin = 1`.

## Literature

Exact values (reporting only — per `docs/DESIGN.md` §2.2 they are never a source of theorems
here):

| k | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|
| f(k) | 1 | 4 | 13 | 44 | 160 | unknown, `536 ≤ f(6) ≤ 1836` |

- `S(4) = 44`: Golomb & Baumert, *Backtrack Programming*, JACM 12:4 (1965).
- `S(5) = 160`: Heule, *Schur Number Five*, AAAI 2018 (DRAT-verified SAT proof).
- `536 ≤ S(6)`: Fredricksen & Sweet, *Symmetric sum-free partitions and lower bounds for
  Schur numbers*, Electron. J. Combin. 7 (2000).

General upper bounds. Every known upper bound goes through the `k`-colour Ramsey number for
triangles: `S(k) ≤ R_k(3) − 2` (Schur's reduction — colour the edge `{i,j}` of `K_N` by the
colour of `|i − j|`).

- `R_k(3) ≤ k·(R_{k−1}(3) − 1) + 2` (pigeonhole at a vertex), `R_1(3) = 3`, which solves to
  `R_k(3) ≤ ⌊e·k!⌋ + 1` and hence **`S(k) ≤ ⌊e·k!⌋ − 1`** — Schur (1916); the standard
  textbook bound. This is V001 below.
- Small exact/best-known Ramsey values: `R_2(3) = 6`, `R_3(3) = 17` (Greenwood–Gleason 1955),
  `R_4(3) ≤ 62` (Fettes, Kramer, Radziszowski, *An upper bound of 62 on the classical Ramsey
  number R(3,3,3,3)*, Ars Combin. 72 (2004)), `R_5(3) ≤ 307`, `R_6(3) ≤ 1838`
  (Radziszowski's dynamic survey *Small Ramsey Numbers*). The quoted `S(6) ≤ 1836` is
  exactly `R_6(3) − 2`.
- Asymptotically nothing better than `e·k!` is known for `R_k(3)`, so `⌊e·k!⌋ − 1` is
  essentially the state of the art for `S(k)` as a formula, even though the truth is believed
  to be exponential (`S(k) ≥ c·3.17^k` from Fredricksen–Sweet-type constructions).
- The recurrence's first three steps are *exact* (`R_1 = 3`, `R_2 = 6`, `R_3 = 17`), so any
  improvement of the closed form must beat `R_4(3) ≤ 66`, i.e. reproduce the
  computer-assisted `≤ 62`. The classical parity/regularity refinement
  (`R_k(3) ≤ k(R_{k−1}(3) − 1) + 1` when `k·(R_{k−1}(3)−1)+1` and `R_{k−1}(3)−1` are both
  odd) never triggers on this chain: with `a_j := R_j(3) − 1` one has `a_j` odd exactly when
  `j` is even (`j ≥ 2`), and the argument needs `a_{k−1}` odd with `k` even.

## Starting record

`Records/Upper/V000/`: `3·k! − 2`, from the weakened recurrence `R_k(3) ≤ 3·k!` proved in
`SqueezeBench/Problems/Schur/Finite.lean`.

## V001 — `baseline claude-opus-5`

**Bound.** `record k = ram k − 2` where `ram 0 = 2` and `ram (k+1) = (k+1)·(ram k − 1) + 2`;
so `ram k = R_k(3)`-bound `= ⌊e·k!⌋ + 1` for `k ≥ 1` and `record k = ⌊e·k!⌋ − 1`.
Values: `ram = 2, 3, 6, 17, 66, 327, 1958, 13701, …`,
`record = 0, 1, 4, 15, 64, 325, 1956, 13699, …`.

**Idea.** `Finite.lean` already proves the sharp pigeonhole step
`monoTriangle_step : MonoTriangle N k → MonoTriangle ((k+1)(N−1)+2) (k+1)`; V000 only used it
through the weaker closed form `3·k!`. V001 iterates the step itself from
`monoTriangle_one : MonoTriangle 3 1`, i.e. keeps the recurrence instead of solving it
generously:

- `monoTriangle_ram : MonoTriangle (ram (k+1)) (k+1)` — induction on `k`, one application of
  `monoTriangle_step` per colour.
- `forces_of_monoTriangle : MonoTriangle (N+1) k → Forces k N` — the gap colouring of
  `forces_factorial`, with the Ramsey bound left as a parameter (same proof, generalised).
- `forces_ram : Forces (k+1) (ram (k+1) − 1)`, then `f_le_of_forces` gives
  `f k ≤ ram k − 2`.
- `improves`: `ram k ≤ 3·k!` by induction (the step needs `k ≥ 1`; `k = 0, 1` are checked
  directly, `ram 1 = 3 = 3·1!`), then `Nat.sub_le_sub_right`.
- `strict`: witness `k = 4`, `64 < 70`.

**Why.** It improves the record at every `k ≥ 3`, by a factor `e/3 ≈ 0.906` asymptotically
and by a growing absolute amount (`k = 5`: 358 → 325, `k = 10`: `1.09·10^7 → 9.86·10^6`),
and it is the strongest general bound the literature offers.

**Witness.** `k = 4` (`70 → 64`).

**Elaboration trap met on the way.** `MonoTriangle` is a `def` whose body starts with
`∀ {V} [Fintype V] [DecidableEq V]`. Writing `exact h` (or `have h := lemma …` with no type
ascription) for a goal/term of type `MonoTriangle _ _` makes Lean instantiate those binders
eagerly and fail with *typeclass instance problem is stuck `DecidableEq ?m`*. The fix used
everywhere in V001: `intro V _ _ col hsym hcard` first and apply the lemma to
`col hsym hcard`, or pass the `MonoTriangle` term as an explicit argument to another lemma.

## Comparison

| k | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|
| V000 (start) | 1 | 4 | 16 | 70 | 358 | 2158 | 15118 |
| **V001** | 1 | 4 | 15 | 64 | 325 | 1956 | 13699 |
| f(k) (known) | 1 | 4 | 13 | 44 | 160 | ≥ 536 | ? |

## What the next improvement would take

The recurrence is exact up to `k = 3`, so a better *closed form* has to beat
`R_4(3) ≤ 66`; the known `R_4(3) ≤ 62` is a computer search over critical colourings and is
out of reach of the 200000-heartbeat budget (and of the "no search" rule). Three directions
that look plausible, in order of expected cost:

1. **Kill the extremal case of the Schur reduction.** For a sum-free `k`-partition of
   `[1,N]` one has `N = Σ_c |A_c|` and `|A_c| ≤ R_{k−1}(3) − 1 =: a_{k−1}` (the differences
   inside `A_c` avoid colour `c`, so `A_c` carries a mono-triangle-free `(k−1)`-colouring).
   `N = k·a_{k−1}` therefore forces *every* colour degree at *every* vertex of the gap
   colouring on `{0,…,N}` to be exactly `a_{k−1}`, which forces
   `|A_c ∩ [1,v]| = |A_c ∩ [N+1−v, N]|` for all `v`, i.e. the colouring is symmetric under
   `x ↦ N+1−x`. **This route now closes** — see *The parity finish* below, which turns the
   symmetry into a contradiction for every odd `k ≥ 3`. The Lean cost is the reflection
   bookkeeping plus a Ramsey-style bound on each `|A_c|`, which needs `monoTriangle_step`'s
   induced-colouring construction redone for a subset of `[1,N]`.
2. **Exploit that our `Forces` is the strong Schur condition** (`x = y` allowed, so
   `x, 2x` never share a colour) — the Ramsey chain never uses it. Note
   `WS(4) = 66 > 64`, so the doubling constraint is exactly what makes the Ramsey bound
   applicable to `S` and not to the weak Schur numbers; there should be slack there. At the
   two innermost levels there is none: `σ(1) = 2` and `σ(2) = 5` are attained
   (`X = {0,1,2,3,4}` with `A = {1,4}`, `B = {2,3}`), so the first place to look is
   `σ(3) < 16`, i.e. no 16-element set whose difference set carries a sum-free 3-colouring.
   That would give `S(k) ≤ k·σ(k−1)` with `a_4 ≤ 61` and a ~6% gain for every `k ≥ 4`.
3. **A single-point improvement at `k = 3`** (`15 → 14`, or `→ 13` which is exact): prove
   `Forces 3 15` by hand. `decide` is not an option (`3^15` colourings is a search, and the
   budget forbids it), so this is a written case analysis on the colour equalities of
   `1, 2, 4, 8, …`; expect a long but elementary proof. Improves one `k` only, which the
   brief discourages, but it is the only route that needs no new mathematics.

**Problems hit.** Only the `DecidableEq ?m` elaboration trap recorded under V001; the
computation budget was never close (V001 uses 5659 of 200000 heartbeats in all).

## The parity finish — `S(k) ≤ ⌊e·k!⌋ − 2` for every odd `k ≥ 3`

Found by `baseline claude-opus-5` in a later session; at the time **stated and checked on
paper only**. It is now formalised and accepted as **V002** below (in a shortened form that
needs the neighbourhood bound at one vertex only). It completes direction 1 above and beats V001 at
infinitely many `k` (all odd `k ≥ 3`), by 1 at each: `k = 3`: `15 → 14`; `k = 5`:
`325 → 324`; `k = 7`: `13699 → 13698`.

Write `a_j := ram j − 1`, so `a_1 = 2`, `a_j = j·a_{j−1} + 1`, giving
`a = 2, 5, 16, 65, 326, 1957, 13700, …` and `record k = a_k − 1`. Suppose `[1,N]` has a
sum-free `k`-colouring with `N = k·a_{k−1}` — the extremal case V001 cannot exclude. Colour
the pair `{u,v}` of `V = {0,…,N}` by `c(|u−v|)`; no mono triangle, as in `forces_of_monoTriangle`.

1. **Neighbourhood bound.** In a mono-triangle-free `k`-colouring, the colour-`c`
   neighbourhood of any vertex `v` carries a mono-triangle-free colouring in the `k−1`
   colours `≠ c` (an inside edge of colour `c` would close a triangle at `v`), so it has at
   most `a_{k−1}` vertices. This is the content of `monoTriangle_step`, but that lemma only
   ever uses it at *one* vertex; the formalisation has to expose it as a standalone lemma
   about an arbitrary vertex.
2. **Every degree is extremal.** At vertex `v` the colour-`c` degree is
   `|A_c ∩ [1,v]| + |A_c ∩ [1,N−v]|`, and summing over `c` gives `v + (N−v) = N = k·a_{k−1}`.
   With `k` summands each `≤ a_{k−1}`, all are exactly `a_{k−1}`.
3. **Symmetry.** `v = 0` gives `|A_c| = a_{k−1}`; general `v` then gives
   `|A_c ∩ [1,v]| = |A_c ∩ [N+1−v, N]|`, and differencing at `v` and `v−1` gives
   `v ∈ A_c ↔ N+1−v ∈ A_c`. Every class is invariant under `x ↦ N+1−x`.
4. **Parity.** For odd `k ≥ 3`, `k−1` is even, so `a_{k−1}` is odd (`a_j` is odd exactly for
   even `j`), hence `N = k·a_{k−1}` is odd and `N+1` is even. The involution `x ↦ N+1−x` on
   `[1,N]` then has exactly one fixed point, `(N+1)/2`. An invariant set avoiding it has even
   size, so **at most one** class has odd size — but all `k ≥ 3` classes have size `a_{k−1}`,
   which is odd. Contradiction, so `N ≤ k·a_{k−1} − 1` and `f k ≤ ram k − 3`.

Two checks that the argument is not proving something false:

- **`k = 2` survives, as it must.** `a_1 = 2` is even, `N = 4` is even, `N+1 = 5` is odd, the
  involution `x ↦ 5−x` is fixed-point free, and the extremal `{1,4}, {2,3}` is indeed
  symmetric with even classes. No contradiction, and `S(2) = 4 = record 2`.
- **Even `k` survives too.** For even `k`, `a_{k−1}` is even and `N` is even, so step 4 has
  nothing to say; `k = 4` (`N = 64`, classes of 16) and `k = 6` (`N = 1956`, classes of 326)
  are untouched. The gain is at odd `k` only.

Note this is *not* the classical Ramsey parity refinement, which the section above correctly
reports as never triggering on this chain: that one needs an `a_{k−1}`-regular graph on an
odd number of vertices, i.e. `a_k` odd *and* `a_{k−1}` odd, which never co-occur. The
argument here is about the *Cayley* structure of the gap colouring — the reflection
`x ↦ N+1−x` of the interval, which has no Ramsey counterpart — and its parity condition,
`a_{k−1}` odd with a fixed point present, does occur, at exactly the odd `k`.

**Cost estimate.** Steps 1 and 2 are the work: step 1 means refactoring
`monoTriangle_step`'s `Fin.succAbove` induced-colouring construction into a reusable
`neighbourhood_card_le`, and step 2 is a `Finset.sum` argument with `k` terms pinned to their
common upper bound. Steps 3 and 4 are short (`Finset.card` of an invariant set under a
fixed-point-free involution is even — Mathlib has `Finset.even_card_of_involutive`-style
tooling via `Finset.card_eq_two_mul_iff`/`Equiv.Perm` orbits, or do it by hand pairing
`x` with `N+1−x`). Nothing in it computes, so the 200000-heartbeat budget is not a concern.
As an intermediate, `record k = if k % 2 = 1 ∧ k ≥ 3 then ram k − 3 else ram k − 2` is the
natural shape; a `minWith` fold against V001 keeps `improves` free.

## This session (`baseline claude-opus-5`) — no new version accepted

Time was spent on the three directions above. Directions 2 and 3 were re-confirmed as out of
reach under the budget (direction 3, `Forces 3 15` by hand, is an unavoidable multi-page
colour case analysis once `decide` is excluded; `fin_cases` on `Fin 3` with no WLOG on colour
names multiplies it further). Direction 1 was pushed to a complete paper proof — *The parity
finish* above — but its Lean cost (the standalone neighbourhood bound, refactored out of
`monoTriangle_step`) did not fit the session, and a half-finished record is worth nothing. The
record therefore stands at V001, `f k ≤ ram k − 2 = ⌊e·k!⌋ − 1`.

## V002 — `baseline claude-opus-5`

**Bound.** `record k = if 3 ≤ k ∧ k % 2 = 1 then ram k − 3 else ram k − 2`, i.e.
`S(k) ≤ ⌊e·k!⌋ − 2` for every **odd** `k ≥ 3` and `⌊e·k!⌋ − 1` otherwise. This is *The
parity finish* of the section above, now formalised.
Values: `record = 0, 1, 4, 14, 64, 324, 1956, 13698, …` for `k = 0, …, 7`.

**Idea.** Write `a = ram (k−1) − 1`, so `ram k = k·a + 2` and the open case of V001 is a
sum-free `k`-colouring `col` of `[1, N]` with `N = k·a`. Fix such a colouring and work in
the gap colouring of `{0, …, N}`.

- `card_le_of_gaps_ne`: any `X ⊆ [0, N]` whose pairwise gaps all avoid one colour `c₀` has
  `|X| ≤ a`. The pairs of `X` are coloured by `col` of the gap through
  `Function.invFun (Fin.succAbove c₀)`, i.e. in `k−1` colours; if `|X| ≥ ram (k−1)` then
  `V001.monoTriangle_ram` gives a monochromatic triangle in `X`, whose three gaps are a
  monochromatic `x + y = z` inside `[1, N]`, contradicting sum-freeness. This is the
  standalone neighbourhood bound the previous session was missing; phrasing it about a set
  of *naturals* rather than a vertex subtype avoids redoing `monoTriangle_step`.
- Applied at the single vertex `v = m − 1`, where `m = (N+1)/2`: the colour-`c`
  neighbourhood is `{v − x | x ∈ A_c ∩ [1, v]} ∪ {v + x | x ∈ A_c ∩ [1, m]}`, and its gaps
  avoid `c` (three cases, each an instance of sum-freeness). Hence
  `|A_c ∩ [1, m−1]| + |A_c ∩ [1, m]| ≤ a` for every `c`.
- Summing over the `k` colours gives `(m − 1) + m = N = k·a`, so **every** one of those `k`
  sums is exactly `a`. Since `[1, m] = insert m [1, m−1]`, that says
  `a = 2·|A_c ∩ [1, m−1]| + [m ∈ A_c]`.
- Parity: `a = (k−1)·(ram (k−2) − 1) + 1` is odd when `k−1` is even, and then `N = k·a` is
  odd too, so `m` is an integer in `[1, N]`. `a` odd forces `[m ∈ A_c] = 1` for *every*
  colour `c`, while `∑_c [m ∈ A_c] = 1`. With `k ≥ 3` that is a contradiction.

**Why this shape.** The paper proof in the previous section derives the full reflection
symmetry `x ∈ A_c ↔ N+1−x ∈ A_c` and then counts. That is not needed: taking the
neighbourhood at the *single* vertex `m − 1` (whose two half-intervals are `[1, m−1]` and
`[1, m]`, straddling the midpoint) produces the parity relation directly, which cut the
formalisation to about 250 lines and made it fit the session.

**Witness.** `k = 3` (`15 → 14`). Improves V001 at infinitely many `k` — every odd `k ≥ 3`
— by exactly `1` at each.

**Cost.** 39493 of 200000 heartbeats in all; heaviest declaration `forces_parity`, 32956.

## Comparison (updated)

| k | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|
| V000 (start) | 1 | 4 | 16 | 70 | 358 | 2158 | 15118 |
| V001 | 1 | 4 | 15 | 64 | 325 | 1956 | 13699 |
| **V002** | 1 | 4 | **14** | 64 | **324** | 1956 | **13698** |
| f(k) (known) | 1 | 4 | 13 | 44 | 160 | ≥ 536 | ? |

## What the next improvement would take, after V002

1. **Even `k`.** The parity argument is silent there: for even `k`, `a = ram (k−1) − 1` is
   even and `N = k·a` is even, so the reflection `x ↦ N+1−x` of `[1,N]` has no fixed point
   and no contradiction arises. Pushing `k = 4` (`64 → 63`) needs a different obstruction —
   the natural candidate is to use the neighbourhood bound at *two* vertices at once and
   compare the induced `(k−1)`-colourings, or to run the parity argument one level down,
   inside a colour class.
2. **Iterating the parity gain.** V002 subtracts 1 only at the top level. If the extremal
   analysis were carried out for the `(k−1)`-colouring living on a colour class, `a` itself
   would drop by 1 for odd `k−1`, which would compound through the recurrence and give a
   gain growing like `k!/j!`. The obstacle is that the neighbourhood of a vertex is *not*
   an interval, so the reflection used here is unavailable; one needs the Ramsey-level
   statement `R_k(3) ≤ k·(R_{k−1}(3) − 1) + 1` under a parity hypothesis, which the
   literature says does not trigger on this chain.
3. Directions 2 and 3 of the pre-V002 list (the strong-Schur slack `σ(3) < 16`, and
   `Forces 3 15` by hand) are unchanged, except that V002 already reaches `14` at `k = 3`,
   so the hand case analysis there would now have to reach the exact value `13`.

**Problems hit in this session.** None beyond the `DecidableEq ?m` trap recorded under
V001, which is why `card_le_of_gaps_ne` is stated for `X : Finset ℕ` and applies
`V001.monoTriangle_ram` to the coercion `↥X` with all arguments explicit. The only failed
step on the first build was a missing `omega` after an `if_neg` rewrite.

## Session notes — `baseline claude-opus-5` (V003 attempt, no new version accepted)

Starting point: V002 accepted, `record k = if 3 ≤ k ∧ k % 2 = 1 then ram k - 3 else ram k - 2`.
The open target is even `k` (direction 1 of the list above). The session was short and no
V003 was finished; what follows is what was established on paper, so the next attempt does
not have to rediscover it.

### The extremality cascade

In the open case `N = k·a_{k-1}` the equality analysis of V002 does not stop at the top
level — it propagates all the way down the Ramsey chain:

1. At **every** vertex `v ∈ {0,…,N}` of the gap colouring, `∑_c d_c(v) = v + (N−v) = N =
   k·a_{k−1}` with each `d_c(v) = |A_c ∩ [1,v]| + |A_c ∩ [1,N−v]| ≤ a_{k−1}`, so every one
   of the `k·(N+1)` degrees equals `a_{k−1}` exactly.
2. Differencing at `v` and `v−1` (`d_c(v) − d_c(v−1) = [v ∈ A_c] − [N+1−v ∈ A_c]`) gives the
   **reflection symmetry** `x ∈ A_c ↔ N+1−x ∈ A_c` for every class.
3. Taking `v = 0`, the neighbourhood is `A_c` itself, of size exactly `a_{k−1}`, and pairs
   inside `A_c` avoid colour `c` — so `A_c` with the induced `(k−1)`-colouring is a
   *critical* mono-triangle-free colouring. Repeating step 1 inside it: for every `x ∈ A_c`
   and every `d ≠ c`, `|{y ∈ A_c : col |x−y| = d}| = a_{k−2}` exactly. Since
   `a_{k−1} − 1 = (k−1)·a_{k−2}`, this is forced, and it recurses down to `a_1 = 2`.

So the extremal configuration is rigid at every level, not just the top. That is a lot of
structure to work against, and it is the natural raw material for the even-`k` case.

### Why the parity trick does not extend to even `k` as it stands

For even `k`: `a_{k−1}` is even and `N = k·a_{k−1}` is even, so `(N+1)/2` is not an integer
— the vertex V002 uses does not exist — and the reflection `x ↦ N+1−x` on `[1,N]` is
fixed-point free, so counting invariant classes gives nothing. One level down the parities
flip back (`a_{k−2}` is *odd* when `k` is even), which is why step 3 above looks promising,
but the involution available there is the wrong one: the reflection `ρ(y) = N+1−y`
preserves `A_c` and its colours, yet maps the `d`-neighbourhood of `x` to that of `ρ(x)`,
not of `x`. The reflection about `x` itself, `y ↦ 2x−y`, *is* colour-preserving and
fixed-point free on the punctured neighbourhood, but does not preserve `A_c`. Finding one
involution that does both is the missing step; it would give a contradiction for even `k`
of exactly V002's shape, since each of the `k−1` neighbourhood classes has odd size
`a_{k−2}`.

One concrete extra constraint that falls out of the symmetry and is not yet used:
`c(x) = c(N+1−x)` plus sum-freeness forces, for every odd `y ∈ [1,N−1]`,
`c(y) ≠ c((N+1−y)/2)` — the difference of `x` and its mirror is `N+1−2x`, which therefore
cannot carry `x`'s colour.

### Correction to direction 2 above (the strong-Schur slack)

`σ(j)` must be read as the largest `|X|`, `X ⊆ ℕ`, whose *internal* difference set carries a
sum-free `j`-colouring — **not** `X ∪ {0}`. With that reading `σ(1) = 2`, `σ(2) = 5`
(attained by `A = {5,6,7,8,9}` inside the extremal `S(3) = 13` partition, differences
`{1,2,3,4}` split as `{1,4} , {2,3}`), the bound that comes out is `N ≤ k·σ(k−1)`, and
`k = 3` gives `13 ≤ 15`, consistent. Reading it as `X ∪ {0}` gives `S(3) ≤ 12`, which is
false; a previous draft of this section invited that slip. The gain still requires
`σ(3) ≤ 15`, which remains a search and remains out of budget.

### State

Record unchanged at V002. No files were added or edited outside this report.
