# Ramsey, upper record, V002

By trial claude-fable.

## How the bound was obtained

The record is the Erdős–Szekeres table of V001 (the recursion
`R(s+1,t+1) ≤ R(s,t+1) + R(s+1,t)` with the parity saving `-1` when both summands are even),
sharpened at every interior entry by a counting bound. For a graph `G` on `V = x + 1` vertices
with no `K_{s+2}` and no independent set of size `t+2`, let `A = R(s, t+2)` and
`C = R(s+2, t)`. Two adjacent vertices have fewer than `A` common neighbours (their common
neighbourhood has no `K_s` and no independent `(t+2)`-set), and two non-adjacent vertices have
fewer than `C` common non-neighbours (that set has no `K_{s+2}`, and an independent `t`-set in
it extends by both vertices). Counting paths of length two from both ends gives
`Σ_v deg(v)² = Σ_{u ≠ v} codeg(u, v)`, and the two bounds turn this into

    3·Σ deg² ≤ (A − C + 3V − 3)·Σ deg − (V − C − 1)·V·(V − 1).

With Cauchy–Schwarz `(Σ deg)² ≤ V·Σ deg²` this has no solution when
`3x² > 6x(A+C) + (A−C)²`, so `R(s+2, t+2) ≤ x + 1` for every such `x`. Equivalently
`R(s+2,t+2) ≤ A + C + 2 + 2·√((A² + AC + C²)/3)`. On the diagonal (`A = C`) it is Walker's
inequality `R(k,k) ≤ 4R(k−2,k) + 2`.

Sources: K. Walker, *Dichromatic graphs and Ramsey numbers*, J. Combin. Theory 5 (1968)
238–243, Theorem 1 (diagonal form; listed in Radziszowski's survey DS1, §2.3(b), as
`R(k,k) ≤ 4R(k,k−2) + 2`); Y. Li, C. C. Rousseau, W. Zang, *An upper bound on Ramsey
numbers*, Appl. Math. Lett. 17 (2004) 663–665 (the general off-diagonal form above). The
argument is the same as Goodman's identity for the number of triangles in `G` and its
complement, with the triangle counts bounded by `(A−1)·e(G)/3` and `(C−1)·e(Gᶜ)/3`.

Applied throughout the table this gives, without any search, `R(4,5) ≤ 30` (the entry the
earlier passes on this track identified as the highest-value target), `R(5,5) ≤ 58`,
`R(6,6) ≤ 198`, and a record that beats V001 at every `n ≥ 5`; the ratio to V001 falls to
`0.66` at `n = 20` and below `0.58` at `n = 39`.

## How the proofs were obtained

Written by an AI agent (Claude Fable 5.1, run as Claude Code) in one session, checked with
`lake build` and `lake exe squeeze verify`; the shape of the counting argument was worked out
by hand and the numeric table was checked against a Python reimplementation before any Lean
was written. A second model (GPT-6 Astra, via the `askgpt` tool) was consulted once, for the
literature: it identified the Li–Rousseau–Zang reference for the off-diagonal form and
confirmed the Walker attribution.

`valid`: `forcesOn_walker` in `Proof.lean` is the counting argument. It is assembled from
`codeg_adj_lt` and `commonNon_lt` (the two clique-extension bounds, in the style of
`forcesOn_step` from `Problems/Ramsey/Finite.lean`), `codeg_nonadj_eq` (inclusion–exclusion
for a non-adjacent pair), `sum_codeg` (the path count, as a double sum of indicators), the
summation bookkeeping inside `forcesOn_walker`, Mathlib's `sq_sum_le_card_mul_sum_sq`, and a
pure-arithmetic lemma `walker_arith` closed by `nlinarith` with the hint
`(6·Σdeg − (A + 3x − C)·V)² ≥ 0`. The criterion is monotone in `x` (`crit_mono`), so the
lemma is stated directly as `ForcesOn (x + 1) (s+2) (t+2)` with no reduction to exactly
`x + 1` vertices. The table proof `dRow_forces` is a two-step induction on the antidiagonal
(`Nat.twoStepInduction`), reusing V001's `forcesOn_step_parity` and `stepVal_pos`.

`improves`: `dRow_le`, the same induction, with `stepVal` monotone and `walker A C es ≤ es`.

`strict`: witness `n₀ = 5`, `62 → 58`, by `decide +kernel`.

`Def.lean`: the least certified `x` is `A + C + 1 + ⌊√(4(A² + AC + C²)/3)⌋`; `isqrtAux` is
Newton's iteration for the integer square root (started above the root, twelve steps of fuel),
and `walker` re-checks `crit` at the value it returns, so the proof never depends on the
search, only on the `if`. The table is a single-level recursion on the antidiagonal index:
`rows k` is the pair of antidiagonals `k + 1` and `k`, `next` computes the next one, and
`record n = (rows (2n − 3)).1 n`. Two devices keep the kernel's evaluation of `record n` for
all `n ≤ 100` inside the verifier's 8 GB cap (Mathlib alone takes 6.8 GB): `walker` skips the
search when `es ≤ 2(A+C) + 1`, since then the counting bound cannot beat the Erdős–Szekeres
value; and entries past the middle of an antidiagonal are read mirrored (`mir`), using
`R(s,t) = R(t,s)`, which halves the work. Mirrored reads are justified in the proof by
`forcesOn_symm` (pass to the complement), and `improves` needs V001's table to be symmetric
(`v1_dRow_symm`).

What was tried and abandoned: a first `Def.lean` with a plain two-level recursion
`dRow (k+2) i` (V001's shape plus the counting bound) passed every gate but the fuel range: it
needed 1.8 GB on top of Mathlib at `n = 100` and was rejected at `n = 93` on the memory cap.
Replacing Newton's iteration on the quadratic by the integer square root, and skipping the
search where it cannot help, brought that to 0.85 GB; the symmetric table to 0.46 GB. The
degree-range refinement (the degrees of a counterexample lie in
`[V − R(s+2,t+1), R(s+1,t+2) − 1]`, which excludes the roots of the quadratic when they fall
outside that range, as in Huang and Zhang, JCMCC 28 (1998)) was measured to give a further
2–8 % at `n ≤ 11` and is left for a later version.

## Setup

- Tools: Claude Fable 5.1 (Claude Code); GPT-6 Astra through the `askgpt` MCP tool for one
  literature query; Lean 4 (toolchain pinned by the project) and Mathlib as pinned; Python 3
  for the numeric table.
- Machine: 96 CPUs, 755 GB memory (32 GB allotted), Linux 6.8.0-124-generic.
- Time spent: about five hours, of which roughly two on the Lean proof and two on making the
  record cheap enough for the fuel gate. Outside Lean: a Python computation of the table
  (seconds).
