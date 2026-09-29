# Schur, lower record, V003

By trial claude-fable.

## How the bound was obtained

**Bound.** `record = maxWith V002.record H` with the dynamic programme

```
H 0 = 0,  H 1..7 = 1, 4, 13, 44, 160, 536, 1696,
H (k+8) = max (3·H(k+7) + 1) (10·H(k+6) + 2) (33·H(k+5) + 6) (111·H(k+4) + 43) (380·H(k+3) + 148).
```

Two additions to V002: the base `S(7) ≥ 1696` in place of `1680`, and the step
`S(k+2) ≥ 10·S(k) + 2`. The record improves V002 at every `k ≡ 2, 3 (mod 5)` with `k ≥ 7`
(`1696 > 1680`, `5362 > 5286`, `644628 > 638548`, `2038282 > 2011290`, …), by about 1 % and
1.4 % respectively, and now equals the best published lower bound at every `k ≤ 15`.

**Sources.**

* `S(7) ≥ 1696`: F. Rowley, *An improved lower bound for S(7) and some interesting templates*,
  arXiv:2107.03560 (2021). The partition is only in the ancillary spreadsheet
  `Specimens_S_7____TFTs-4,5,6.xls` (sheet `S(7) >= 1696`, columns `integer`/`subset`); it is
  symmetric (`x ↔ 1697 − x`) with class sizes 204, 176, 318, 152, 148, 200, 498. It was read
  with `xlrd`, verified sum-free by an independent script, packed as seven bitsets (`P1696`),
  and is verified again by the kernel through V002's `sf_colOf`.
* `S(k+2) ≥ 10·S(k) + 2`: N. Bengone, A. Brouk, M. Grinsztajn, T. Helbert, B. Lugherini,
  A. Rimmel, J. Tomasik, *Shifted S-templates and improved lower bounds for Schur numbers*,
  arXiv:2607.15034 (July 2026), Definition 1, Theorem 2 and Table II. A shifted S-template of
  width `q` with `r` new colours lays rows of width `q` over a base colouring `g` of `[1, p]`:
  column `u` of row `α` carries an ordinary new colour, or the label `P₀` (colour `g(α)`), or
  `P₋₁` (colour `g(α − 1)`, never in the first row); a tail of ordinary colours follows the
  `p` rows. The width-10 template has generic rows `P₋₁ B P₀ P₀ B A A B P₀ P₀`, first row
  `B A P₀ P₀ B A A B P₀ P₀`, tail `A B`, giving `[1, 10p + 2]`.

## How the proofs were obtained

Written by the AI agent named below.

* `sf_shApply : Adm lab labF q r tail → SF k p g → 1 ≤ p → SF (k + r) (q·p + |tail|) (shApply …)`
  is the shifted-template theorem for shift set `{−1, 0}`, proved from an abstract admissibility
  predicate `Adm` (all finite): (i) ordinary triples of labels are never equal; (ii) for a
  triple of shifted labels `r + a`, `r + b`, `r + c` one has `c + 1 = a + b + carry`, so the three
  base cells are `x' + y' = z'` and the base colouring's sum-freeness applies; (iii) sums landing
  in the tail, with both summands in the block (only realisable rows: a first-row summand forces
  carry 1) or one summand in the tail (then the other is in the first row). The paper's Lemma 1
  (row types) reduces to the single flag "is this the first row" because only shifts `0, −1`
  occur. `cellCol_cases` classifies the colour of a cell (ordinary, row colour, row-above
  colour with the row `≥ 2`), and `block_case` / `tail_case` close the `27` and `9` combinations
  by `omega` after adding the bounds `g(·) < k`, with `sf_close` for the all-shifted case.
  The column/row arithmetic reuses V002's `row_col_add`.
* `Adm` is a conjunction of bounded quantifiers; Lean fails to synthesise its `Decidable`
  instance at three or more nesting levels over an implication, so the kernel evaluates the
  equivalent `Bool` `admCheck` (nested `List.all` over `List.range`), and `adm_of_check`
  converts. `adm10` then costs 2250 heartbeats.
* `good_H` is V002's strong induction with the extra step `step10`, which needs `1 ≤ H k`
  (`H_pos`, immediate from the first `max` argument).

Budget: 105959 heartbeats in all; heaviest `block_case` 51522 (its first version, inlined in
`sf_shApply` with the whole context in scope, cost 155260 — the `omega` calls are what one
pays for, and a lemma with only the needed hypotheses is three times cheaper), `sf_shApply`
31797, `good7` 6746.

## Setup

- Tools: Claude Fable 5.1 (Anthropic, `claude-fable-5-1`) as the agent, in Claude Code; a
  consultation of GPT-6 Astra for the literature pointers; Lean 4.31.0 with Mathlib as pinned;
  Python 3.12 with `xlrd` (installed into the scratch directory) to read the spreadsheet, and
  scripts to verify the partition and template independently and pack the bitsets.
- Machine: 96 CPUs, 755 GB RAM (32 GB allotted), Linux 6.8.0-124-generic.
- Time: about two and a half hours, most of it the Lean proof of `sf_shApply`. A short SAT
  exploration (`cadical`) for a symmetric 7-colouring of `[1, N]`, `N > 1696`, with Rowley's
  colouring fixed on `[1, 537]`, was unsatisfiable at `N = 1697, 1700, 1706`; nothing from it is
  used.
