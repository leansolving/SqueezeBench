# Roth, upper record, V006

By trial claude-fable.

## The bound

    record n = min (V005.record n) (v n),
    v n = max (2 * ((2n + 20) / 11)) (2 * ((2n + 11) / 11) + 1)

i.e. Moser's second bound `r₃(n) ≤ 4n/11 + O(1)`: `100 → 40`, `1000 → 366` (V005: `42`, `402`).
It beats V005 from `n = 27` on at 62 of the values `n ≤ 100` and at every `n ≥ 49`.

## How the bound was obtained

The V005 argument bounds `r₃(n)` through the number of distinct pairwise sums of the larger
parity class `A` (`|A| = t ≥ ⌈k/2⌉`) of a 3-AP-free `S ⊆ [0, n)`: their halves are distinct
integers below `n` outside `S`, so `k + |A +̂ A| ≤ n`. V005 used Moser's `|A +̂ A| ≥ 3t - 7`.
Moser's paper also proves `r₃(n) < 4n/11 + 5` by a longer count; the version formalised here,
suggested in a consultation and verified by enumeration before formalisation, is

    2 |A +̂ A| ≥ 7t - 20   for every 3-AP-free t-set A,

proved by induction removing the two smallest elements: for `t ≥ 7`, at least **seven** sums
involving `a₀` or `a₁` are distinct and are not sums of two of `a₂, …` (the *seven-point lemma*;
sums with an index `≥ 7` are larger than `a₁ + a₆`, so only `a₀, …, a₆` matter), and for `t ≤ 6`
Moser's `3t - 7` suffices. With `e₀ + e₁ = k`, `2k + 7e_r ≤ 2n + 20` for both classes gives
`k ≤ v n`.

The seven-point lemma. `[12] < [13] < [23] < [24] < [34]` are four new sums. One of
`[14], [15]` and one of `[25], [26]` is new (Moser's interleaving argument), and they differ. A
third new sum is `[27]`, `[17]` or `[16]` unless each equals an earlier sum (`6 + 10 + 6`
candidates); if in addition neither pair `[14], [15]` nor `[25], [26]` is entirely new, the
possible coincidences form a case tree whose 128 leaves are all contradictory: 88 by the order
`a₀ < … < a₆` alone, 40 by an explicit three-term progression forced by two coincidences. The
tree was explored with an SMT solver (z3, as a search tool outside Lean); the Lean proof
`hard` replays it as nested `rcases`, each leaf closed by `omega` or by one instance of
3-AP-freeness, so nothing is searched at check time.

Sharper constants are possible (`7t - 18`, with base cases `|A +̂ A| ≥ 9, 12` at `t = 5, 6`;
verified by enumeration) but the `t = 6` base needs a second 56-leaf tree; not included.

## How the proofs were obtained

By hand with the AI agent named below, from scratch files checked with `lake env lean`,
except the leaf-by-leaf proof of `hard`, which was generated from the solver's case tree by a
short Python script (the branching order and the certificate of each leaf) and then checked
by Lean. `omega` is kept away from large disjunctions by `clear`-ing them in the branches
where they are not needed, and the four smallest sums, the choice of `u`, `v` and the
assembly of the seven-element set are separate lemmas.

The whole file costs about 100000 heartbeats (`lake exe squeeze budget-probe`); the heaviest
declarations are `seven_new` and `hard` (about 30000 each).

## Setup

- Tools: Claude Code with the model Claude Fable 5.1 (`claude-fable-5-1`) as the agent, two
  consultations of GPT-6 Astra via the `askgpt` tool (literature; reconstruction of Moser's
  `4/11` argument as a deletion lemma), Lean 4 (v4.31.0) with the pinned Mathlib, Python 3.12
  and z3 for enumerating small 3-AP-free sets and exploring the case tree.
- Machine: 96 cores, 755 GB RAM (32 GB budget for this job), Linux 6.8.0-124-generic.
- Time: about three hours after V005 was accepted. No search ran inside Lean.
