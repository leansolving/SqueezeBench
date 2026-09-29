# ExC4, lower record, V006

By trial claude-fable.

This record predates the `REPORT.md` template. This file was written after the run by the
supervising session, from the agent's transcript and the V006 section of
`evaluation/runs/ExC4-Lower/REPORT.md`.

## How the bound was obtained

The Erdős–Rényi polarity graph `ER_q` (Erdős–Rényi 1962, Brown 1966) for every prime power `q`:
`q² + q + 1` vertices, `q (q + 1)² / 2` edges, no `C₄`. For each `n` the record takes the best of
two constructions: `⌊n / N_q⌋` disjoint copies of `ER_q` plus a graph on the remaining vertices,
and `ER_q` with vertices of minimum degree deleted one at a time (each deletion from a graph with
`m` edges on `t` vertices loses at most `⌊2m/t⌋` edges). This gives order `½ n^{3/2}`, against the
linear bound of V005.

## How the proofs were obtained

By the agent, autonomously. `ER_q` is defined over an arbitrary finite field in an affine model
(the points `(a, b)` and `q + 1` points at infinity), so the absence of `C₄` (`ER_free`: no two
distinct vertices have two common neighbours) and the degree count are proved once for every
field and then instantiated with `GaloisField p k`. General lemmas on `f`: extremal graphs exist,
superadditivity through disjoint sums (`f_superadd`), and deletion of a vertex of minimum degree
(`f_del`). Prime powers are recognised by a trial-division test that the kernel evaluates, with a
soundness proof. The agent consulted `askgpt` once, on the literature: exact values beyond
`n = 40`, and constructions between consecutive prime-power orders.

## Setup

- Tools: Claude Code 2.1.281 running Claude Fable 5.1 (`claude-fable-5-1`) at maximum effort,
  with shell, file and web tools and one consultation tool (`askgpt`: GPT-6 Astra through
  OpenRouter). Lean 4.31.0 and Mathlib v4.31.0 as pinned.
- Machine: 2 × AMD EPYC 9274F (96 threads), 755 GB memory, of which the agent could use 32 GB;
  Ubuntu 24.04.
- Time: 35 minutes from the start of the session to the accept. No computation outside Lean is
  recorded for this version.
