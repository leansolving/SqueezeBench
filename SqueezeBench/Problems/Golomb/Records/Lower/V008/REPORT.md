# Golomb, lower record, V008

By trial claude-opus-5.5.

## How the bound was obtained

**Bound.** A certificate checker. Sort the marks `a₀ < … < a_{m−1}`, let `L' = a_{m−1} − a₀`
and `b_r = (a_r − a₀) + (a_{m−1} − a_{m−1−r})`. For `u + 1 ≤ s` let `E(u, s)` be the pairs of
order `≤ u` together with **all** pairs inside the first `s` or the last `s` marks (`2s ≤ m`).
Its `n = M_u + (s−1−u)(s−u)` differences are distinct, and

```
n (n + 1) + 2 ∑_r neg(u,s,r) b_r ≤ u (u + 1) L' + 2 ∑_r pos(u,s,r) b_r,
neg = (u − r) + (s − 1 − u − r),  pos = [r < s] (r − u)      (truncated subtraction).
```

A certificate is a list of weighted triples `(λ, u, s)`. If the weighted coefficients satisfy
`POS_r ≤ NEG_r` for all `r`, the `b_r` can be replaced by V007's lower bound
`H _ 2 (r+1) ≤ b_r` (the first and last `r + 1` marks as a separated family), giving

```
L ≥ ⌈ (∑ λ n(n+1) + 2 ∑_r (NEG_r − POS_r) · H _ 2 (r+1)) / ∑ λ u(u+1) ⌉ .
```

The record builds the certificate `s_j = s₀ + j`, `u_j = 1 + ⌊j(s₀+J−3)/J⌋`,
`λ_j = (J+1)² − j²` (`0 ≤ j ≤ J`), repairs it top-down with plain Lindström sets wherever a
net coefficient is positive, checks it, and takes the best of six `(s₀, J)` around
`(3⌊√m⌋/4, 5⌊√m⌋/4 − 5)`; `record = max (V007.record) (that)`.

**How it was found.** The inequalities `∑_{E} d ≥ |E|(|E|+1)/2` for every set `E` of pairs
form the classical LP relaxation of the Golomb ruler problem (Lorentzen–Nilsen, Hansen–
Jaumard–Meyer, Shearer). Solving that LP numerically by cutting planes showed it is well above
V007 (`m = 50`: 1899.4 against 1875) and that its optimal dual uses nested sets of the form
"order `≤ u` plus the pairs inside the dense end pieces", mixed over many `u`. Restricted
to the sets `E(u, s)`, whose sums are linear in `L'` and the `b_r` (checked numerically, then
proved), the LP can be solved for large `m` with few variables; its optimal certificates are a
chain as above with slowly decreasing weights. The quadratic weights, the linear `u_j` and the
greedy repair were found by search in Python; they reach almost the LP value (`m = 100`: 8210
against 8214.0; `m = 400`: 145114 against 145133.3).

The LP gain over V007 grows like `m^{3/2}` in this range (`0.049 m^{3/2}` at `m = 100`,
`0.062 m^{3/2}` at `m = 1600`), i.e. the certificates improve the second-order term of
`m² − 2m^{3/2}` itself, not only the `O(m)` term.

**Numbers.** Improves V007 at every `m` from 16 to 150 except 32–35 (checked in Lean), and at
381 of `1 ≤ m ≤ 400` (Python model of the same record); e.g. `20: 254 → 256`,
`27: 493 → 496`, `50: 1875 → 1888`, `100: 8165 → 8210`, `150: 19075 → 19162`,
`200: 34676 → 34820`, `400: 144671 → 145114`.

**Witness.** `n₀ = 100`: `8165 → 8210`.

## How the proofs were obtained

By hand, written by the agent; it built at the first attempt. `F m u s` is the index set of
`E(u, s)` as a filter of `range m ×ˢ range m`, with V006's indexing `(j, i) ↦ (i, i+j+1)`.
`ext_id` computes `∑_F D` and `|F|` by induction on `s`: the base `s = u + 1` is the Lindström
set (V007's `order_eq` summed, `double_sum`); the step adds the `s − u` pairs ending at `a_s`
and the `s − u` pairs starting at `a_{m−1−s}`, and
`(a_s − a_i) + (a_{m−1−i} − a_{m−1−s}) + b_i = b_s` term by term. `item_le` adds the Sidon
distinctness (V006's `card_mul_le_sum`), `cert_sum` sums a certificate by induction on the list,
and `certBound_le_span` uses the check and `bLow_le` (V007's `H_le` for `{0, m−1−r}`).
Everything the record computes is checked by the record itself; the proof only needs the
soundness of the check.

Cost: 68318 heartbeats in all; heaviest `ext_id` 29576.

## Sources

No code from outside sources. Mathematics: B. Lindström, *An inequality for B₂-sequences*,
J. Combin. Theory 6 (1969) 211–212; the subset-sum LP relaxation of Golomb rulers
(P. Hansen, B. Jaumard, C. Meyer, *On lower bounds for numbered complete graphs*, Discrete
Appl. Math. 94 (1999) 205–225; C. Meyer, B. Jaumard, *Equivalence of some LP-based lower bounds
for the Golomb ruler problem*, Discrete Appl. Math. 154 (2006) 120–144), used here only as the
idea to explore numerically. V006's and V007's definitions and lemmas and V001's `isqrt` are
reused.

## Setup

- Tools: Claude Opus 5.5 (`claude-opus-5-5`) as the agent in Claude Code; Python with SciPy
  (HiGHS) for the LP experiments and the parameter search. The LP solutions are not used by the
  record or the proof.
- Machine: 96 cores (`nproc`), 755 GB RAM (`free -g`; the session is capped at 32 GB),
  Linux 6.8.0-124-generic.
- Time: about two hours.
