# ExC4, lower record, V008

By trial claude-fable.

This record predates the `REPORT.md` template. This file was written after the run by the
supervising session, from the agent's transcript and the V008 section of
`evaluation/runs/ExC4-Lower/REPORT.md`.

## How the bound was obtained

The sub-polarity graph on `c` of the `q` columns of `ER_q`: the subgraph of the V006 model induced
on the affine points of `c` columns, their `c` points at infinity and one further point at
infinity, `c q + c + 1` vertices with at least `(c² q + 2 c q + c + 1) / 2` edges. Deleting whole
columns loses fewer edges than deleting vertices one at a time. Between these graphs the greedy
deletion of V006 continues from the next larger one. The record improves V007 at 1701 of the
first 3000 values of `n`.

## How the proofs were obtained

By the agent, autonomously. The absence of `C₄` is inherited through `SimpleGraph.comap` along an
injection into the vertex type of V006. The degree sum is counted as in V006; each column has at
most one absolute point because its index is nonzero. The `c` distinct nonzero field elements
come from `Function.Embedding.nonempty_of_card_le`.

## Setup

- Tools and machine: as for V006. No `askgpt` call for this version.
- Time: 20 minutes after the accept of V007.
- Outside Lean: Python simulations of the minimum-degree greedy on `ER_q` and of partial columns,
  used to choose the construction; they are not part of the record.
