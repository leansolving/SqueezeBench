# CapSet, lower record, V003

By trial claude-fable.

## How the bound was obtained

The record is `max (V002 n) (112 ^ (n / 6) · head (n % 6))` with `head = [1, 2, 4, 9, 20, 45]`
for `n % 6 = 0, …, 5`: a cap of size 112 in `F₃⁶` on every block of six coordinates, the
product rule `f m · f n ≤ f (m + n)` of V001, and the small caps of V001/V002 on the leftover
coordinates. Growth rate `112^(1/6) ≈ 2.1955` per dimension, up from `45^(1/5) ≈ 2.1411`.

The 112-cap is the classical one: the 56-cap of Hill in `PG(5,3)` (R. Hill, *On the largest
size of cap in S₅,₃*, Atti Accad. Naz. Lincei Rend. 54 (1973); *Caps and codes*, Discrete
Math. 22 (1978)), whose cone `{±v}` in `F₃⁶` is the unique 112-cap of `AG(6,3)`
(Potechin 2008 shows 112 is the maximum). It was constructed here as a hemisystem of the
elliptic quadric `Q⁻(5,3)`: the 112 points of `Q(x) = x₀x₁ + x₂x₃ + x₄² + x₅²` carry 280
lines, and a 56-subset meeting every line in exactly two points is a cap (Segre's hemisystem
of `H(3,9)` under the Klein-type duality). A small depth-first search in Python found such a
subset in seconds; the resulting 112 vectors were checked independently to be a cap before
anything was written in Lean.

## How the proofs were obtained

All by the AI agent, with the literature notes of the earlier submitters in
`evaluation/runs/CapSet-Lower/REPORT.md` as the starting point.

The hard part is not the mathematics but checking a 112-point cap inside the 200000-heartbeat
budget: the earlier records' pair test (`|A|²` evaluations of `y + y - x` on `Fin n → ZMod 3`)
was measured at about 24 heartbeats per pair, i.e. `≈ 150000` for the 6216 unordered pairs.
`Proof.lean` instead works on base-3 *codes* and a 729-bit *membership mask* `M`:

* the reflection `y ↦ -(x + y)` of `F₃⁶` acts on codes digit by digit, and on each digit it is
  a transposition of the three values (`v ↦ -xᵢ - v`); on the mask, a transposition of the
  three slices along one axis is three `&&&` with constant slice masks and two shifts;
* so `refl 6 x M` (six such steps) is the mask of `-(x + A)`, and `A` is a cap iff
  `M &&& refl 6 x M = 1 <<< x` for every `x ∈ A`: the only point of `A` of the form
  `-(x + y)` with `y ∈ A` is `x` itself (from `y = x`).

The kernel evaluates this with GMP arithmetic on 729-bit numbers; `codes_pair` (all 112
reflections) costs about 700 heartbeats and the whole file about 8000. The correctness proof
is general in the dimension `n` (`threeAPFree_of_mask`): slice masks are geometric sums
(`Nat.geomSum_eq`) whose bits are characterised by `Nat.testBit_two_pow_mul_add`, the
transposition lemma `testBit_swp` is a case analysis on the digit, and `testBit_reflUpTo`
composes the axes by induction. The decoding `dec n : ℕ → (Fin n → ZMod 3)` is injective on
codes below `3 ^ n`, and `dec n (thd x y n) = -(dec n x + dec n y)`. `improves` and `strict`
are the `maxWith` idiom; `key` is the strong induction of V001/V002 with step 6.

Because the machinery is dimension-independent, a later record only needs a new code list, a
new mask and the same three `decide +kernel` lines.

## Setup

- Tools: Claude Fable 5.1 (claude-fable-5-1) as the agent, with GPT (askgpt) consulted once on
  the literature; Python 3.12 for the hemisystem search and the mask; Lean 4.31.0 / Mathlib as
  pinned by the project.
- Machine: 96 cores, 755 GB RAM (32 GB allotted), Linux 6.8.0-124-generic.
- Time: about two hours, of which the search took seconds; no computation outside Lean other
  than the Python search and its independent cap check.
