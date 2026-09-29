# Off-diagonal Ramsey numbers `R(3, k)`

`f(k)` is the least `N` such that every 2-colouring of the edges of `K_N` contains a triangle in
the first colour or a `K_k` in the second.

This is the off-diagonal Ramsey problem with the first size fixed at `3`. Its asymptotic *order*
is settled — `R(3,k) = Θ(k² / log k)`, by Ajtai–Komlós–Szemerédi above (1980) and Kim below
(1995) — so unlike the diagonal problem the open question is the **leading constant**, not the
growth rate.

`nMin = 2`.

## Known values

**Reporting only. These are never a source of theorems** (`docs/DESIGN.md` §2.2). `f` is
noncomputable here, so none of these is machine-checked.

| k | f(k) |
|---|---|
| 2 | 3 |
| 3 | 6 |
| 4 | 9 |
| 5 | 14 |
| 6 | 18 |
| 7 | 23 |
| 8 | 28 |
| 9 | 36 |

`k = 10` is open: `40 ≤ R(3,10) ≤ 41`.

Citation: Radziszowski, *Small Ramsey Numbers*, Electronic J. Combinatorics Dynamic Survey DS1;
OEIS A000791. The per-value attributions (Greenwood–Gleason, Kéry, Kalbfleisch, McKay–Zhang,
Grinstead–Roberts) are in DS1 and have not been checked against it here.

## Formalisation status

`f` is defined in `Def.lean` as `sInf {N | SqueezeBench.Ramsey.Forces N 3 k}`.

**Nothing about the forcing relation is restated.** `Ramsey/Def.lean` already declares
`Forces N s t` with separate clique sizes for the two colours — it had to, because the
Erdős–Szekeres induction needs that form — so this problem is the same relation at `s = 3`.
Two consequences, and they are why this problem was cheap:

- **There is no `Finite.lean`.** `Ramsey.forces_exists 3 k` *is* the statement that the set
  defining `f` is nonempty, so `wellPosed` is a one-liner and stays in `Def.lean`.
- **The upper seed needed no new induction.** `Ramsey.forcesOn_choose s t` reads
  `ForcesOn (C(s+t, s)) (s+1) (t+1)`; at `s = 2` that is `C(k+1, 2)` vertices forcing a triangle
  or a `K_k`.

## Seeded records

| direction | record | `k=2` | `k=3` | `k=9` |
|---|---|---|---|---|
| lower | `pin nMin (fun k => 2k − 1)` | **3** | 5 | 17 |
| upper | `C(k+1, 2)` | **3** | 6 | 45 |

True values: `3`, `6`, `36`.

**The two records meet at `k = 2`.** `lower(2) = upper(2) = 3`, so the conjunction of
`Lower.V000.valid` and `Upper.V000.valid` *is* a proof that `R(3,2) = 3` — machine-checked, with
no citation anywhere in the chain. At `k = 3` the gap is `1`, so one lower-side improvement
determines `R(3,3) = 6` as well.

The lower seed is the parity graph on `2k−2` vertices — the complete bipartite graph between
evens and odds, written on `Fin N` so that no re-indexing is needed. It is triangle-free because
among any three vertices two share a parity, and a clique in its complement has constant parity,
so `x ↦ x / 2` bounds it by `k−1`.

## Where the next improvement lies

**The lower side, and the gap widens fast**: `2k−1` against a truth of `Θ(k²/log k)`, so by
`k = 9` the seed gives `17` against `36`. The literature route is Kim's `Ω(k²/log k)`, a genuine
research formalisation; the intermediate `R(3,k) ≥ c·(k/log k)^{3/2}` constructions are the
realistic next step, and a point patch at a single `k` from a known value is admissible and much
cheaper.

On the upper side, `C(k+1,2) ≈ k²/2` against `~k²/log k` means improving it is the
Ajtai–Komlós–Szemerédi argument or an explicit weakening of it. But note the upper seed is
already **exact at `k = 2` and `k = 3`**, so the first upper improvement must target `k ≥ 4`.

## Current state

| | |
|---|---|
| Well posed | **yes** — `wellPosed`, from `Ramsey.forces_exists` |
| Lower record | `Records/Lower/V007/` — beats V006 at witness `1683` (trial claude-fable; based on V005, V006, 2026-09-25) |
| Upper record | `Records/Upper/V004/` — beats V003 at witness `12` (trial claude-fable; based on V002, V003, 2026-09-24) |
| Live | **yes** — both Challenges open at `V001`; `squeeze audit Ramsey3` accepts both seeds |

## Record history

One row per accepted version, oldest first, appended by `lake exe squeeze accept`.
The author is the `name` in the record's `metadata.toml`.

### Upper

| version | date | author | witness | value at the witness |
|---|---|---|---|---|
| V001 | 2026-09-24 | baseline claude-opus-5; based on V000 | 9 | 45 → 42 |
| V002 | 2026-09-24 | trial claude-fable; based on V001 | 10 | 51 → 46 |
| V003 | 2026-09-24 | trial claude-fable; based on V002 | 8 | 32 → 31 |
| V004 | 2026-09-24 | trial claude-fable; based on V002, V003 | 12 | 63 → 62 |

### Lower

| version | date | author | witness | value at the witness |
|---|---|---|---|---|
| V001 | 2026-09-24 | baseline claude-opus-5; based on V000 | 9 | 17 → 21 |
| V002 | 2026-09-24 | baseline claude-opus-5; based on V000, V001 | 9 | 21 → 23 |
| V003 | 2026-09-24 | baseline claude-opus-5; based on V000, V001, V002 | 9 | 23 → 27 |
| V004 | 2026-09-24 | baseline claude-opus-5; based on V000, V001, V002, V003 | 10 | 27 → 29 |
| V005 | 2026-09-25 | trial claude-fable; based on V001, V003, V004 | 17 | 53 → 79 |
| V006 | 2026-09-25 | trial claude-fable; based on V001, V003, V004, V005 | 9 | 31 → 36 |
| V007 | 2026-09-25 | trial claude-fable; based on V005, V006 | 1683 | 23761 → 24390 |
