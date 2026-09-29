# ExC4, lower record, V007

By trial claude-fable.

This record predates the `REPORT.md` template. This file was written after the run by the
supervising session, from the agent's transcript and the V007 section of
`evaluation/runs/ExC4-Lower/REPORT.md`.

## How the bound was obtained

Explicit `C₄`-free graphs for `8 ≤ n ≤ 49` from the Afzaly–McKay database
(`users.cecs.anu.edu.au/~bdm/data/extremal.html`): the extremal graphs for `n ≤ 40` and the best
known graphs for `41 ≤ n ≤ 49`. The greedy deletion of V006 extends each of them downwards. One
edge between two `C₄`-free graphs lies on no cycle, so `f a + f b + 1 ≤ f (a + b)`, and the block
decompositions of V006 gain one edge per bridge. The record equals `f(n)` for every `n ≤ 40`.

## How the proofs were obtained

By the agent, autonomously. A generic theorem `table_bound` turns a list of neighbourhood
bitmasks into a lower bound on `f` at the list's length, provided the kernel confirms the list's
check: symmetry, irreflexivity, and the absence of `C₄` by a pairwise test on the bitwise
intersections. The 42 tables cost about 69000 heartbeats together. The bridge lemma uses
`SimpleGraph.sum` and the addition of one edge. A `simp` call that unfolded 49 deletion chains
ran out of heartbeats and was replaced by evaluation in the kernel.

## Setup

- Tools and machine: as for V006. No `askgpt` call for this version.
- Time: 25 minutes after the accept of V006.
- Outside Lean: the agent downloaded the sparse6 files from the Afzaly–McKay database and decoded
  them to bitmasks with a Python script. An iterated-greedy search in Python (40 s per `n`) for
  `50 ≤ n ≤ 62` stayed below V006 and was not used.
