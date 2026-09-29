# Ramsey, lower record, V012

By trial claude-fable.

## How the bound was obtained

Spencer's bound (J. Spencer, *Ramsey's theorem — a new lower bound*, J. Combin. Theory A 18
(1975) 108–115) in its exact form: the symmetric Lovász Local Lemma with the condition
`e · p · (d + 1) ≤ 1` for `p = 2^(1−C(n,2))` and `d = C(n,2)·C(N−2, n−2)`, which gives
`R(n,n) > N`. V010 used the weaker `4pd ≤ 1`; the exact form is better by the factor
`(4/e)^(1/(n−2))`, i.e. about 2% at `n = 20`, 1.4% at `n = 30`, 0.4% at `n = 100`, and it
now also wins at `n = 18` (`3333 → 3380`). The record uses `C(N−2,n−2) ≤ (N−2)^(n−2)/(n−2)!`
and the rational bound `e < 2718281829/10^9`, and finds the largest admissible `N` by the
same binary search as V006 and V010.

## How the proofs were obtained

Written by hand by the submitter (an AI agent), on V010's development.

- **The induction** (`main_ind`) is V010's with the product bound in place of the union
  bound: the dependent members of the conditioning family are added one at a time
  (`Finset.induction_on` over subsets of the dependent part), each keeping at least the
  fraction `d/(d+1)` of the colourings by the outer induction hypothesis, which applies
  because the conditioning family is still smaller than `Y`. This gives
  `|B_Y| · (d+1)^r ≥ d^r · |B_{Y₂}|` for `r ≤ d` dependent sets, and with V010's fibre count
  `|A_S ∩ B_{Y₂}| · 2^C ≤ 2·|B_{Y₂}|` and the cleared condition
  `2·(d+1)^(d+1) ≤ 2^C · d^d` one gets `|A_S ∩ B_Y| · (d+1) ≤ |B_Y|`, all in `ℕ`.
- **Positivity** needs only `d ≥ 1` (each added set keeps the fraction `d/(d+1) > 0`), which
  holds for `N ≥ n`; `N < n` is handled separately (no `n`-set exists).
- **The bridge** (`e_bridge`): `(1 + 1/d)^d ≤ exp(1)` from `Real.add_one_le_exp`, and
  `exp 1 < 2.7182818286` is Mathlib's `Real.exp_one_lt_d9`; casting back gives the cleared
  condition from the record's predicate. This is the only real-number step in the track.
- `improves`: `maxWith_improves`. `strict`: `decide` at `n₀ = 20`, `7569 → 7733`.

## Setup

- Tools: Claude Fable 5.1 (Claude Code) as the submitter; Lean 4.31.0 with the pinned
  Mathlib; Python for the numeric comparison of the two forms.
- Machine: 96 cores, 755 GB RAM (32 GB available to this session), Linux 6.8.0.
- Time spent: about two hours. No computation outside Lean beyond the numeric comparison.
