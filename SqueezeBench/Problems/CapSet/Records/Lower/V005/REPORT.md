# CapSet, lower record, V005

By trial claude-fable.

## How the bound was obtained

The record is `max (V004 n) (best n)`, where `best` is the dynamic programme of V004 with an
infinite family of extra rows: for every `m ≥ 1`, a cap of size

```
fam m = m · 12 · 112 ^ (m - 1)      in dimension 6 m.
```

This is the *extended product construction* of Edel (*Extensions of generalized product
caps*, Des. Codes Cryptogr. 31 (2004)) in the formulation of Tyrrell (*New lower bounds for
cap sets*, Discrete Analysis 2023:20, Section 2), instantiated with the admissible set
`I(m, m-1)`:

* an **extendable collection** `(A₀, A₁, A₂)` of caps in `F₃ᵈ` satisfies E1: `x + y + z ≠ 0` for
  `x, y ∈ A₀`, `z ∈ A₁ ∪ A₂`, and E2: `x + y + z ≠ 0` for `x ∈ A₀`, `y ∈ A₁`, `z ∈ A₂`
  (Definition 2.4);
* a set `S ⊆ {0,1,2}^m` is **admissible** if distinct `s, t` have a coordinate with `sᵢ = 0 ≠ tᵢ`
  and three distinct vectors have a coordinate whose values form `{0,1,2}`, `{0,0,1}` or `{0,0,2}`
  (Definition 2.5);
* **Lemma 2.7**: `⋃_{s ∈ S} A_{s₁} × ⋯ × A_{s_m} ⊆ F₃^{dm}` is then a cap.

Tyrrell's Lemma 2.14 gives the collection in `F₃⁶` with `|A₀| = 12`, `|A₁| = |A₂| = 112`: `A₀`
the twelve vectors of weight 1, `A₁ = D ∪ R`, `A₂ = D' ∪ R`, with `D` (`D'`) the weight-3
vectors supported on a block (a non-block) of the 2-(6,3,2) design
`{123,124,135,146,156,236,245,256,345,346}` and `R` the weight-6 vectors with an even number
of ones (the printed incidence matrix in the paper has a typo in its third row; the design is
taken from the block list). `I(m, m-1)` is the set of the `m` vectors with a single zero at
position `r`, ones before it and twos after it (Lemma 2.12); the union has `m` disjoint
products of sizes `12 · 112^(m-1)`.

`fam m` beats `112^m` as soon as `12 m > 112`, i.e. `m ≥ 10`: the record improves at `n = 60`
(`112^10 → 120 · 112^9`), at every multiple of 6 from there on, and, through the products of
the dynamic programme, at every `n ≥ 60`. The improvement factor `12 m / 112` is unbounded.
Witness `n₀ = 60`.

## How the proofs were obtained

By the AI agent; GPT (askgpt) was consulted for a transcription of Tyrrell's definitions and
of the construction of Lemma 2.14, and every claim was then checked in Lean or in Python.

* `isCap_ext` is Lemma 2.7, proved for an arbitrary additive group of blocks: the three
  labels of a zero-sum triple are equal (each block is in a cap), two are equal (the pair
  condition and E1), or all differ (the triple condition, then E1 or E2 after reordering the
  sum; `Extendable.e2'` handles the six orders by `fin_cases`).
* `card_ext` is the size formula: the pieces over distinct labels are disjoint because
  `A₀ ∩ (A₁ ∪ A₂) = ∅` follows from E1 with `x = y = z` in characteristic 3.
* The collection is verified by the mask method of V003: each `Aᵢ` is a cap (`codesᵢ_pair`),
  and E1, E2 are the mask identities `mask₁ &&& refl 6 x mask₀ = 0`, `mask₂ &&& refl 6 x mask₀ = 0`
  and `mask₂ &&& refl 6 x mask₁ = 0` for the twelve `x ∈ A₀` (`no_sum_of_mask`). The whole
  verification of the collection is a few thousand heartbeats.
* `Sm_admissible` is the admissibility of `I(m, m-1)` (the median index of three distinct
  positions carries the pattern `{0,1,2}`), `tri_inj` its size, `card_ext_Sm` the count.
* `flatHom` flattens `Fin m → Fin 6 → ZMod 3` to `Fin (m * 6) → ZMod 3` (an injective
  additive map; `IsCap.map` carries caps along it), and `card_le_f` connects `IsCap` with
  Mathlib's `ThreeAPFree` and the problem's `le_f_of_threeAPFree`.
* The dynamic programme reuses the scheme of V004 (`dp_getD`, `term_le`, `foldl_le`).

## Setup

- Tools: Claude Fable 5.1 (claude-fable-5-1) as the agent; GPT (askgpt) for the literature
  transcription; Python 3.12 to build the collection and its masks (with an independent check
  of E1/E2); Lean 4.31.0 / Mathlib as pinned.
- Machine: 96 cores, 755 GB RAM (32 GB allotted), Linux 6.8.0-124-generic.
- Time: about two hours.
