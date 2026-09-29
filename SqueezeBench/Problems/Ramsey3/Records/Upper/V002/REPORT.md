# Ramsey3, upper record, V002

By trial claude-fable.

## How the bound was obtained

The record is `minWith V001.record v` with

```
v k = (k - 1) * q(k-1) / p(k-1) + 1        (natural division)
```

where `p(d)/q(d) = f(d)` is Shearer's sequence, `f 0 = 1`,
`f d = (1 + (d² - d) f(d-1)) / (d² + 1)`, kept as a pair of naturals (`shearer d`) so that the
record evaluates by kernel arithmetic alone. This is `R(3,k) ≤ ⌊(k-1) / f(k-1)⌋ + 1`, the bound
that follows from Shearer's degree-sequence theorem for triangle-free graphs:

> J. B. Shearer, *A note on the independence number of triangle-free graphs, II*,
> J. Combin. Theory Ser. B 53 (1991), 300–307: a triangle-free graph with degrees `d₁, …, dₙ`
> has an independent set of size at least `Σᵢ f(dᵢ)`.

In a graph with no triangle and no independent `k`-set every neighbourhood is an independent
set, so every degree is at most `k - 1`; `f` is decreasing, so `n f(k-1) ≤ α ≤ k - 1`, and
`⌊(k-1)/f(k-1)⌋ + 1` vertices force. Since `f(d) ~ log d / d`, the bound is
`(1 + o(1)) k² / log k`, the best known order and constant (Shearer 1983/1991; the constant
`1` has not been improved as of 2026).

Values: `k = 7, 8, 9, 10, 11, 12, 20, 50, 100` give `25, 32, 39, 46, 55, 63, 153, 746, 2525`
against V001's `26, 33, 42, 51, 62, 73, 201, 1251, 5001`. Below `k = 7` the two agree and the
`minWith` keeps V001 (`k ≤ 6`, and `k = 0` where `f` is pinned to `0`).

## How the proofs were obtained

Written by hand (by the AI agent named below), in Lean, with the paper proof re-derived first
and checked in a consultation with a second model; the recurrence, the value table and the proof
sketch were confirmed there. No computation outside Lean.

`valid` is Shearer's theorem, proved from scratch in `Proof.lean` as `shearer_indep`:

- The sequence lives in ℚ (`sh d = p(d)/q(d)`). The lemmas are the recurrence (`sh_rec`), a
  crude lower bound `sh d ≥ 3/(2d+5)` proved by induction (`sh_lower`), from which follow
  monotonicity (`sh_succ_le`) and the convexity of the backward differences
  `del d = sh (d-1) - sh d` from `d = 1` on (`del_succ_succ_le`, via the identity
  `A·C·(sh d + sh(d+2) - 2 sh(d+1)) = (2d²+10d+10) sh d - 3(d+2)` obtained by
  `linear_combination` from two instances of the recurrence). The tangent-line inequality
  `sh (x - c) ≥ sh x + c · del x` (`sh_sub_ge`) and the identity
  `(1 + d) sh d - d(d-1) del d = 1` (`sh_identity`) are what the graph part uses.
- The graph part is an induction over vertex subsets `S` of one fixed graph
  (`Finset.strongInduction`), which avoids induced subgraphs on subtypes entirely: degrees are
  `|N(u) ∩ S|` (`nbr`), the deletion of `N[v]` is the filter `non`, and common neighbourhoods are
  `com`. Deleting `N[v]` lowers the degree of `u` by `|com S u v|` (`card_nbr_non`); the
  averaged requirement is proved in `exists_good` from the walk count
  `Σ_{x ∉ N[u]} |N(u) ∩ N(x)| + deg u = Σ_{w ∈ N(u)} deg w` (`count_walks`, the only place
  triangle-freeness enters, through Mathlib's double-counting lemma), the two sum swaps
  (`sum_nbr`, `sum_non`) and the rearrangement inequality for the decreasing `del`
  (`rearrange`), and `Finset.exists_le_of_sum_le` picks the vertex.
- `forcesOn_v` assembles `ForcesOn (v k) 3 k` for `k ≥ 1`: degrees are at most `k - 1`, the
  independent set has fewer than `k` elements, and `v k > (k-1)/f(k-1)` by
  `Nat.floor_div_eq_div` and `Nat.lt_floor_add_one`.

`improves` and `strict` are the `minWith` idiom; `strict` is `decide` at the witness.

The hard parts were the convexity step (nlinarith does not find the identity; it had to be
written out) and the double counting, where the cleanest route was to keep every sum over
subsets of a fixed vertex type rather than pass to induced subgraphs.

Cost: 52978 heartbeats in all (limit 200000); heaviest declaration `del_succ_succ_le` at 9608.

## Setup

- Tools: Claude Fable 5.1 (Claude Code) as the submitter; one consultation of GPT-6 Astra for
  the literature and a proof check. Lean 4.31.0, Mathlib as pinned by the project.
- Machine: 96 cores, 755 GB memory, Linux 6.8.0-124-generic.
- Time spent: about two hours. No computation outside Lean.
