# HypercubeC4, upper record, V007

By trial claude-fable.

## How the bound was obtained

**Bound.** Chung's bound (F. R. K. Chung, *Subgraphs of a hypercube containing no small even
cycles*, J. Graph Theory 16 (1992) 273–286, §4), density `→ (2 + √13)/9 ≈ 0.62284`, in an
exact finite form. With `psi u = u(5u−4)(u−4)` for `u ≥ 4` (else `0`) and
`W d u = 32·d(d−1)(d−2) + psi u`, the record is `minWith V006.record v`, where
`v n = min_{2 ≤ c ≤ n+2} bound n c` and, with `D = W(c+1, n−c−1) − W(c, n−c) > 0`,

    bound n c = ⌊ 2ⁿ⁻¹ · (8n(n−1)(n−2) + c·D − W(c, n−c)) / D ⌋

(the edge count of `Qₙ` when `D ≤ 0`). It beats V006 at every `n ≥ 12` (`n = 12`:
`16286 → 16283`; `n = 20`: `6807800 → 6779430`; `n = 100`: density `0.62756`).

**Idea.** Fix a word `x` and three directions `i, j, k`; the block of `x` is the `Q₃` through
`x` in these directions. Call a pair `{i, j}` *blue at `x`* when the two edges of the square
`(i, j)` at `x` that avoid `x` are present. For each block, with `h` its number of full
corners (all three edges present) and, for each isolated corner `v` (no edge), `b(v)` its
number of blue pairs among the three, Chung's Lemma 13 is

    4·h + Σ_{v isolated} (b(v) − 1)² ≤ 8 .

Proof by cases: if some isolated `v` has `b = 3` the six far edges form a hexagon, every
other corner is non-isolated and non-full except the antipode of `v`, which has at most one
edge (two would close a square); otherwise every isolated corner contributes at most `1`, and
`h ≤ 2` with `h = 2` forcing adjacent full corners whose only possible isolated corners have
exactly one blue pair. Summed over the `2ⁿ⁻³` blocks of every ordered triple of directions:

    32·Σ_x d(d−1)(d−2) + Σ_x Σ_{(i,j,k) missing at x} 8(b − 1)² ≤ 8n(n−1)(n−2)·2ⁿ .

**The auxiliary graph.** At `x`, the blue pairs form a graph on the `t = n − d` missing
directions, with degrees `r_j`; a double count gives
`Σ_{triples} (b−1)² = C(t,3) + Σ_j (r_j² − t·r_j/2) ≥ C(t,3) − t³/16`, so the inner sum is at
least `psi(t)/8` (clipped at `0`). Hence `Σ_x W(d(x), n − d(x)) ≤ 8n(n−1)(n−2)·2ⁿ`.

**Convexity.** `d ↦ W(d, n−d)` is a convex sequence (second differences `192d` and
`30u − 18`), so it lies above its secant of slope `D` at `c`; summing over the `2ⁿ` words with
`Σ d(x) = 2m` gives `bound n c`.

**Why.** After V006 (the third moment, which is Chung's Lemmas 4–6), a linear program over
the 828 degree profiles of `C₄`-free subgraphs of `Q₄` gave only `0.6258`, while Chung's
refinement stays inside `Q₃` and reaches `0.6228` with an elementary local lemma. The local
lemma was checked by brute force over the 2902 `C₄`-free subgraphs of `Q₃` before proving it.

## How the proofs were obtained

Written with an AI agent, following V006's style. The block lemma is proved for a block
presented as the eight corners `rel x s` (`s ∈ Bool³`) of an arbitrary word `x`; the sum over
the cube is `1/8` of the sum over all `(x, s)`, each `s` giving an involution of the cube
(`sum_g_le`), which avoids fibres and distinctness proofs. The case analysis re-bases the
block at its special corner (`sum_rel_rebase`) and uses permutation invariance of the weight
(`sum_g_perm12`, `sum_g_perm23`) to reduce the three adjacent-full-corner cases to one.
The auxiliary-graph identity is done over ordered triples with nested `erase` sums
(`sum_pairs`, `swap_outer`, `aux_bound`), the secant bound by a general lemma for convex
sequences (`secant`), and the final arithmetic in ℕ with `nlinarith`.

Nothing was mathematically hard; the effort is in the bookkeeping. GPT-6 Astra was consulted
once, to identify Chung's argument and its local lemma.

## Setup

- Tools: Claude Fable 5.1 (Claude Code); one consultation of GPT-6 Astra; Python 3 with scipy
  (profile enumeration and the LP), C for the `Q₄` enumeration.
- Machine: 96 cores, 755 GB RAM, Linux 6.8.0-124-generic.
- Time spent: about four hours. Computation outside Lean: enumeration of the `C₄`-free
  subgraphs of `Q₃` (4096 subsets) and `Q₄` (1.2·10⁹ subgraphs, 23 s in C), two small LPs.
