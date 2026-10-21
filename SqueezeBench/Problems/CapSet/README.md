# Cap sets in F₃ⁿ

A *cap* is a subset of `F₃ⁿ` with no three distinct collinear points — equivalently, no
nontrivial three-term arithmetic progression, equivalently no three distinct `x, y, z`
with `x + y + z = 0`. `f(n)` is the largest size of a cap.

This is the object of the cap-set problem: the growth rate `sup_n f(n)^(1/n)` is bracketed
between `2.2202` (FunSearch, *Nature* **625**, 468–475, 2024) and `2.7551`
(Ellenberg–Gijswijt 2017), and
closing that gap is open.

`nMin = 1`.

## Known values

**Reporting only. These are never a source of theorems.** Values beyond
`n = 2` come from large computer searches.

OEIS A090245 has offset 0 with `a(0) = 1`; that term is omitted here because `nMin = 1`.

| n | f(n) | source |
|---|---|---|
| 1 | 2 | trivial |
| 2 | 4 | exhaustive |
| 3 | 9 | exhaustive |
| 4 | 20 | exhaustive |
| 5 | 45 | exhaustive |
| 6 | 112 | Potechin 2008 |

Citation: OEIS A090245.

`f` here is computable, so the first two entries are machine-checked in `Def.lean`. The
rest are not reachable — the search space is `2^(3^n)`.

## Formalisation status

`f` is defined in `Def.lean` as

```lean
addRothNumber (univ : Finset (Fin n → ZMod 3))
```

**Reuses Mathlib almost entirely.** `ThreeAPFree` over `Fin n → ZMod 3` *is* the cap
condition: it unfolds to `∀ a b c ∈ A, a + c = b + b → a = b`, and over `ZMod 3` a triple
with `a + c = 2b` and `a = b` forces `c = b`, so exactly the nontrivial progressions are
excluded.

**No well-posedness lemma is needed.** Unlike the `sInf`-defined problems this is a
maximum over a finite search space (`Nat.findGreatest`, Mathlib's own extremal-number
idiom), so `f` is total and meaningful with nothing proved first.

What Mathlib does **not** have: anything cap-set specific — no Ellenberg–Gijswijt, no
slice rank, no polynomial method. The Dahmen–Hölzl–Lewis formalization of the solution
(arXiv:1907.01449) is Lean **3**, with no Lean 4 port.

## Seeded records

Both directions are seeded, in `Records/Lower/V000/` and `Records/Upper/V000/`.

| direction | bound | cost |
|---|---|---|
| lower | `pin nMin (fun n => 2 ^ n)` | `{0,1}ⁿ ⊆ F₃ⁿ` is a cap: if `a + c = 2b` coordinatewise with entries in `{0,1}`, then `a = b = c` |
| upper | `2 · 3^(n−1)` | each fibre of a coordinate projection is a line, so a cap meets it twice |

The `pin` on the lower bound is **required**, not cosmetic: `LowerBoundHolds` quantifies
over every `n`, and `f 0 = 0` by the pinning while `2^0 = 1`. The bare `fun n => 2 ^ n` is
not a valid lower record. See `pin_lowerBoundHolds` in `Core/Record.lean`.

The upper record improves on the `3^n` of `f_le_card`: dropping the last coordinate has
fibres `{(w,0), (w,1), (w,2)}`, which satisfy `a + c = b + b` with `a ≠ b`, so a cap meets
each of the `3^(n-1)` fibres at most twice.

What the pair brackets, against the known values above:

| n | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|
| lower | 2 | 4 | 8 | 16 | 32 | 64 |
| f(n) | 2 | 4 | 9 | 20 | 45 | 112 |
| upper | 2 | 6 | 18 | 54 | 162 | 486 |

Both records are exact at `n = 1`, and the lower record is exact at `n = 2`.

## Current state

| | |
|---|---|
| Well posed | **yes** — total by construction |
| Lower record | `Records/Lower/V005/` — beats V004 at witness `60` (trial claude-fable; based on V001, V003, V004, 2026-09-25) |
| Upper record | `Records/Upper/V008/` — beats V007 at witness `4` (trial claude-fable; based on V006, V007, 2026-09-24) |
| Live | yes |

## Record history

One row per accepted version, oldest first, appended by `lake exe squeeze accept`.
The author is the `name` in the record's `metadata.toml`.

### Upper

| version | date | author | witness | value at the witness |
|---|---|---|---|---|
| V001 | 2026-09-24 | baseline claude-opus-5; based on V000 | 2 | 6 → 5 |
| V002 | 2026-09-24 | baseline claude-opus-5; based on V000, V001 | 2 | 5 → 4 |
| V003 | 2026-09-24 | baseline claude-opus-5; based on V000, V001, V002 | 3 | 13 → 12 |
| V004 | 2026-09-24 | baseline claude-opus-5; based on V000, V001, V002, V003 | 3 | 12 → 10 |
| V005 | 2026-09-24 | baseline claude-opus-5; based on V000, V001, V002, V003, V004 | 4 | 32 → 30 |
| V006 | 2026-09-24 | trial claude-fable; based on V000, V001, V002, V003, V004, V005 | 3 | 10 → 9 |
| V007 | 2026-09-24 | trial claude-fable; based on V006 | 9 | 6561 → 6075 |
| V008 | 2026-09-24 | trial claude-fable; based on V006, V007 | 4 | 27 → 20 |

### Lower

| version | date | author | witness | value at the witness |
|---|---|---|---|---|
| V001 | 2026-09-24 | baseline claude-opus-5; based on V000 | 4 | 16 → 20 |
| V002 | 2026-09-24 | baseline claude-opus-5; based on V001 | 5 | 40 → 45 |
| V003 | 2026-09-25 | trial claude-fable; based on V001, V002 | 6 | 90 → 112 |
| V004 | 2026-09-25 | trial claude-fable; based on V001, V002, V003 | 8 | 448 → 512 |
| V005 | 2026-09-25 | trial claude-fable; based on V001, V003, V004 | 60 | 310584820834420916224 → 332769450894022410240 |
