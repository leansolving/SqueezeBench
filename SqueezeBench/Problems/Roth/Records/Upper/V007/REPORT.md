# Roth, upper record, V007

By trial claude-fable.

## The bound

    record n = min (V006.record n) (v n),
    v n = max (2 * ((2n + 18) / 11)) (2 * ((2n + 9) / 11) + 1)

The V006 bound `4n/11 + O(1)` with the additive constant sharpened: one less than V006 at
every `n ≡ 0, 1, 6, 7 (mod 11)` from `n = 22` on (30 of the values `n ≤ 100`, 356 of `n ≤ 1000`);
`100 → 39` (V006: `40`), `1000 → 366` (unchanged).

## How the bound was obtained

V006 proves `2 |A +̂ A| ≥ 7t - 20` for a 3-AP-free `t`-set by deleting the two smallest
elements (seven sums die) with Moser's `3t - 7` as the base for `t ≤ 6`. The true minima at
`t = 5, 6` are `9` and `12` (enumeration), which is exactly what the induction needs for
`2 |A +̂ A| ≥ 7t - 18` at every `t` (the cases `t ≤ 4` follow from `3t - 7`, and the step adds
`14` per two elements). Then `2k + 7⌈k/2⌉ ≤ 2n + 18` for a 3-AP-free `k`-subset of `[0, n)`,
whose largest solution is `v n`.

- `t = 5` (`five_base`): `[12], [13], [23], [24]` and `[34], [35], [45]` are seven distinct
  sums; if `[25] = [34]` both `[14]` and `[15]` are new (each coincidence would force a
  three-term progression), otherwise `[25]` and one of `[14], [15]` are.
- `t = 6` (`six_base`): the sums involving `a₀` or `a₁` outside the sums of `a₂, …, a₅` number
  at least six, the latter number six unless `[36] = [45]`, and in that case a seventh comes
  from `[16]`, from both `[14], [15]` or from both `[25], [26]`; otherwise the coincidences form
  a 13-leaf case tree (`hard6`, found with z3 as in V006, replayed by `rcases`).

The Moser choices `u ∈ {[14], [15]}`, `v ∈ {[25], [26]}` are now proved for enumerations of
any length (`u_gen`, `v_gen`), with sums of larger index excluded by size.

## How the proofs were obtained

By hand with the AI agent named below, reusing V006's `Dt`, `del_two`, `NewQ`, `Q_card` and
V005's `sums`, `key`, `moser_index`; only the base cases and the induction with the new constant
are new. About 80000 heartbeats in all (`lake exe squeeze budget-probe`), `six_base` being the
heaviest declaration (44000).

## Setup

- Tools: Claude Code with the model Claude Fable 5.1 (`claude-fable-5-1`) as the agent, Lean 4
  (v4.31.0) with the pinned Mathlib, Python 3.12 and z3 for enumeration and the case tree.
- Machine: 96 cores, 755 GB RAM (32 GB budget for this job), Linux 6.8.0-124-generic.
- Time: about one and a half hours after V006 was accepted. No search ran inside Lean.
