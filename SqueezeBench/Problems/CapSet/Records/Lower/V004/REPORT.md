# CapSet, lower record, V004

By trial claude-fable.

## How the bound was obtained

The record is `max (V003 n) (best n)` where `best` is a dynamic programme over a table of
verified caps `(d, s)`: `best 0 = 1` and `best k = max over the table of s · best (k - d)`.
The table holds the exact values in dimensions 1–6 (`2, 4, 9, 20, 45, 112`, the caps of
V001–V003) and three larger caps checked in this version:

* `f 7 ≥ 236`: the Calderbank–Fishburn cap (*Maximal three-independent subsets of
  {0,1,2}ⁿ*, Des. Codes Cryptogr. 4 (1994)), rebuilt as `A₁ × {0} ∪ A₂ × {1} ∪ A₀ × {2}` from
  the extendable collection `(A₀, A₁, A₂)` of sizes `(12, 112, 112)` in `F₃⁶` of Edel
  (*Extensions of generalized product caps*, Des. Codes Cryptogr. 31 (2004)) as described by
  Tyrrell (*New lower bounds for cap sets*, Discrete Analysis 2023, Lemma 2.14): `A₀` = the
  twelve vectors of weight 1, `A₁ = D ∪ R`, `A₂ = D' ∪ R`, with `D` the weight-3 vectors
  supported on a block of the 2-(6,3,2) design `{123,124,135,146,156,236,245,256,345,346}`,
  `D'` those supported on a non-block, and `R` the weight-6 vectors with an even number of 1s.
* `f 8 ≥ 512`: the FunSearch cap (Romera-Paredes et al., *Mathematical discoveries from
  program search with large language models*, Nature 625 (2024), 468–475), from the explicit
  construction `build_512_cap` in the published notebook (weight-8 vectors with at least two
  "reflections", and weight-4/5 vectors on prescribed supports).
* `f 9 ≥ 1082`: the FunSearch cap in `F₃⁹`, reproduced by running the paper's greedy
  algorithm with its published priority function for `n = 9`.

Improvements over V003 at every `n ≡ 1, 2, 3 (mod 6)` (factors `236/224`, `512/448`,
`1082/1008`), and at many other `n` through mixed products (`n = 16`: `512² > 20·112²`).
Witness `n₀ = 8`, `448 → 512`.

## How the proofs were obtained

By the AI agent. Each cap is a code list and a membership mask; `V003.threeAPFree_of_mask`
turns the three `decide +kernel` facts into `ThreeAPFree`, and `le_f_of_codes` packages the
cardinality argument. The three reflection tests cost about 1500, 3600 and 8300 heartbeats
(linear in the number of points); the whole file is 43399 heartbeats of the 200000 budget. The dynamic
programme is proved valid by strong induction with the product rule `V001.f_mul_le`:
`dp_getD` relates the list entries to `best`, and `foldl_max_le` bounds the fold. The record is
folded in with `maxWith`, and `strict` is `decide +kernel` at `n = 8`.

All three caps were checked independently in Python before being written into Lean.

## Setup

- Tools: Claude Fable 5.1 (claude-fable-5-1) as the agent; GPT (askgpt) consulted for the
  transcription of Tyrrell's definitions; Python 3.12 for the constructions and the masks;
  Lean 4.31.0 / Mathlib as pinned.
- Machine: 96 cores, 755 GB RAM (32 GB allotted), Linux 6.8.0-124-generic.
- Time: about one hour; no computation outside Lean beyond the Python constructions.
