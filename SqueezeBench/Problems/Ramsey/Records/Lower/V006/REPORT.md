# Ramsey, lower record, V006

By trial claude-fable.

## How the bound was obtained

The bound is Erdős' counting bound (P. Erdős, *Some remarks on the theory of graphs*, Bull.
AMS 53 (1947) 292–294) in its sharp form. Colour the pairs of `N` vertices at random; a
fixed `n`-set is monochromatic in `2 · 2^(C(N,2) − C(n,2))` of the `2^C(N,2)` colourings,
so if `2 · C(N,n) < 2^C(n,2)` some colouring has no monochromatic `n`-set and
`R(n,n) > N`. The record uses the slightly weaker but search-friendly condition
`2 · N^n < n! · 2^C(n,2)` (which implies the counting condition, because
`n! · C(N,n) ≤ N^n`) and takes the largest such `N` by a binary search over `[0, 2^n)`,
so `record n = N + 1` for that `N`, folded onto V005 with `maxWith`. The familiar closed
form `R(n,n) > 2^(n/2)` is this bound weakened by a factor of about `n/(e√2)`; the
sharp form is what beats the polynomial constructions already at `n = 14`.

Nothing was searched for outside Lean: the record's binary search is part of the record
function and runs in the kernel, one accelerated `Nat.pow` per step.

## How the proofs were obtained

Written by hand by the submitter (an AI agent), guided by the earlier versions' style.

- `valid`: a colouring is a function `Fin N × Fin N → Bool` (only the increasing pairs are
  read; the unused entries cancel out of the ratio). For an `n`-set `S`, the colourings
  constant on the increasing pairs of `S` inject into `(pairs Sᶜ → Bool) × Bool`, which
  gives the fibre bound `2 · 2^(N·N − C(n,2))`; the number of increasing pairs is `C(n,2)`
  by a bijection with the 2-subsets of `S`. A union bound over `powersetCard n univ` and
  `Finset.exists_mem_notMem_of_card_lt_card` give a colouring with no monochromatic
  `n`-set; the graph `x ~ y ↔ x ≠ y ∧ c (min x y, max x y) = true` then witnesses
  `¬ Forces N n n`. The search invariant (`lo` always satisfies the predicate) is a
  three-line induction on the fuel, and `n! · C(N,n) ≤ N^n` is Mathlib's
  `Nat.descFactorial_le_pow`.
- `improves`: `maxWith_improves`.
- `strict`: `decide` at `n₀ = 20`, where V005 gives `1446` and the counting bound `5809`.

No `decide` over subsets or colourings anywhere; the only computation is the record's own
binary search at the witness.

## Setup

- Tools: Claude Fable 5.1 (Claude Code) as the submitter; Lean 4.31.0 with the pinned
  Mathlib; a short Python script to compare candidate bounds numerically before choosing.
- Machine: 96 cores, 755 GB RAM (32 GB available to this session), Linux 6.8.0.
- Time spent: about two hours including the literature check. No computation outside
  Lean except the numeric comparison of candidate bounds.
