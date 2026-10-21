# Diagonal Ramsey numbers R(n, n)

`f(n)` is the least `N` such that every 2-colouring of the edges of `K_N` contains a
monochromatic `K_n` — equivalently, every graph on `N` vertices has a clique of size `n`
or an independent set of size `n`.

Known exactly only for `n ≤ 4`. `R(5,5)` is open. The asymptotics are the marquee target —
improvements there are research news.

`nMin = 2`, which avoids the degenerate `n < 2` corners.

## Known values

**Reporting only. These are never a source of theorems.**

`R(1,1) = 1` is omitted: `nMin = 2`, and `f` is pinned to `0` below `nMin`, so listing it
would make the anytime gap compare against a value `f` does not take.

| n | f(n) | source |
|---|---|---|
| 2 | 2 | trivial |
| 3 | 6 | Greenwood–Gleason 1955 |
| 4 | 18 | Greenwood–Gleason 1955 |

`R(5,5)` is unknown; the literature gives `43 ≤ R(5,5) ≤ 46` (upper bound Angeltveit–McKay,
arXiv:2409.15709).

Citation: Radziszowski, *Small Ramsey Numbers* (dynamic survey DS1, rev. 18, 24 Apr 2026).
Do not cite OEIS A120414 for this — since 2023 it has been redefined as
`⌈(3/2)^(n−3)·n(n−1)⌉` and is no longer a sequence of Ramsey numbers at all.

## Formalisation status

`f` is defined in `Def.lean` as `sInf {N | Forces N n n}`, where `Forces N s t` says every
`G : SimpleGraph (Fin N)` has a clique of size `s`, or a clique of size `t` in `Gᶜ`. It is
stated **off-diagonal** because that is what the Erdős–Szekeres induction needs.

Mathlib has the graph-theoretic prerequisites — `SimpleGraph.IsNClique`,
`isNClique_induce_iff`, `IsNClique.insert`, `cliqueFree_compl` — but **no Ramsey numbers**.
(The Formal Conjectures repository has an open issue, #2364, noting exactly this gap.)

**Well posed.** `wellPosed` is proved in `Finite.lean` by the Erdős–Szekeres induction.
The proof runs on `ForcesOn`, a variant quantified over the vertex type with a cardinality
bound, so that passing to a vertex's neighbourhood is an application at the subtype rather
than a re-indexing of `Fin N`. Both bound directions are therefore open, and `le_f` is
unconditional.

`forcesOn_step` is stated in the sharp form `R(s+1,t+1) ≤ R(s,t+1) + R(s+1,t)`, which is
what the binomial bound needs. It carries the side condition `1 ≤ M + N`, since the sharp
count fails when both summands vanish; the base cases are correspondingly `ForcesOn 1 1 t`
and `ForcesOn 1 s 1` rather than the `0` ones, which remain available and are still what
`forcesOn_exists` uses.

An existing Lean 4 formalization, `cruisesong7/formal_ramsey`, also proves this theorem but
carries no license and so could not be used.

## Seeded records

Both directions are seeded, in `Records/Lower/V000/` and `Records/Upper/V000/`.

| direction | bound | source |
|---|---|---|
| lower | `pin nMin (fun n => (n−1)² + 1)` | `n−1` disjoint cliques of size `n−1` |
| upper | `fun n => C(2n−2, n−1)` | Erdős–Szekeres 1935 |

The lower bound is the constructive `R(s,t) > (s−1)(t−1)`, run on `blockGraph`, which joins
two vertices of `Fin N` when their indices agree after division by `k = n−1`. A clique lies
inside one block and a clique of the complement meets each block at most once, so neither
reaches size `n`. Both halves are the same injection into `range k` — by `% k` in the first
case, by `/ k` in the second.

The `pin` on the lower bound is **required**, not cosmetic: `LowerBoundHolds` quantifies
over every `n`, and `f 0 = f 1 = 0` by the pinning while the bare bound is `1` there. See
`pin_lowerBoundHolds` in `Core/Record.lean`. The upper record needs no `pin`: below `nMin`,
`f` is `0`, which is below any bound.

What the pair currently brackets, against the known values above:

| n | lower | f(n) | upper |
|---|---|---|---|
| 2 | 2 | 2 | 2 |
| 3 | 5 | 6 | 6 |
| 4 | 10 | 18 | 20 |
| 5 | 17 | 43 ≤ · ≤ 46 | 70 |

Both records are exact at `n = 2`, and the upper record is exact at `n = 3`.

## Current state

| | |
|---|---|
| Well posed | **yes** — `wellPosed` proved |
| Lower record | `Records/Lower/V013/` — beats V012 at witness `14` (trial claude-fable; based on V007, V012, 2026-09-25) |
| Upper record | `Records/Upper/V002/` — beats V001 at witness `5` (trial claude-fable; based on V001, 2026-09-25) |
| Live | yes |

## Record history

One row per accepted version, oldest first, appended by `lake exe squeeze accept`.
The author is the `name` in the record's `metadata.toml`.

### Lower

| version | date | author | witness | value at the witness |
|---|---|---|---|---|
| V001 | 2026-09-24 | baseline claude-opus-5 | 5 | 17 → 26 |
| V002 | 2026-09-24 | baseline claude-opus-5; based on V001 | 13 | 145 → 226 |
| V003 | 2026-09-24 | baseline claude-opus-5; based on V001, V002 | 10 | 126 → 290 |
| V004 | 2026-09-24 | baseline claude-opus-5; based on V001, V002, V003 | 7 | 69 → 86 |
| V005 | 2026-09-24 | baseline claude-opus-5; based on V002, V003, V004 | 5 | 26 → 38 |
| V006 | 2026-09-25 | trial claude-fable; based on V005 | 20 | 1446 → 5809 |
| V007 | 2026-09-25 | trial claude-fable; based on V006 | 20 | 5809 → 7438 |
| V008 | 2026-09-25 | trial claude-fable; based on V001, V002, V003, V004, V005 | 6 | 38 → 102 |
| V009 | 2026-09-25 | trial claude-fable; based on V008 | 5 | 38 → 43 |
| V010 | 2026-09-25 | trial claude-fable; based on V006, V007 | 20 | 7438 → 7569 |
| V011 | 2026-09-25 | trial claude-fable; based on V001, V002, V003, V005, V008 | 8 | 102 → 282 |
| V012 | 2026-09-25 | trial claude-fable; based on V006, V010 | 20 | 7569 → 7733 |
| V013 | 2026-09-25 | trial claude-fable; based on V007, V012 | 14 | 640 → 647 |

### Upper

| version | date | author | witness | value at the witness |
|---|---|---|---|---|
| V001 | 2026-09-24 | baseline claude-opus-5 | 5 | 70 → 62 |
| V002 | 2026-09-25 | trial claude-fable; based on V001 | 5 | 62 → 58 |
