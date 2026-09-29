# ExGirthFive, upper record, V005

By trial claude-fable.

## How the bound was obtained

Bound: `record n = min( V004.record n, bnd(n, s) )` with `s = ⌊√(n−1)⌋`, `ρ = n − 1 − s²`,
`D = ρ(2s − 1) − 1`, and

```
bnd(n, q) = ⌊ ( D·n·q + n·ρ·(ρ−1) ) / (2·D) ⌋        (D ≠ 0; otherwise C(n,2))
```

i.e. `2m ≤ nq + ⌊ nρ(ρ−1) / (ρ(2q−1) − 1) ⌋`. Against V002's `2m ≤ nq + ⌊nρ/(2q+1)⌋` this
is smaller by about `n(2q + 1 − 2ρ)/(4q²) ≈ (2q + 1 − 2ρ)/4` in `2m` whenever `ρ < q`, which
is about half of all `n`; the gain grows like `√n` and is largest at `ρ = 1` (`n = q² + 2`),
where the bound collapses to `2m ≤ nq`.

The idea is the per-vertex count `∑_{u ∼ x} d(u) ≤ n − 1` of V003 (`nbr_sum_le`), which V004
applied at one vertex of degree `≥ q + 1`. Here it is summed over the set `H` of *all* such
vertices, and the sum is double counted: `∑_{x ∈ H} ∑_{u ∼ x} d(u) = ∑_u d(u)·a(u)` where
`a(u)` is the number of neighbours of `u` inside `H`. Writing `n − 1 = q² + ρ`, `h = #H`,
`T = ∑ (d(u) − q)⁺` and `S = ∑ (q − d(u))⁺`, one has `∑_u a(u) = ∑_{x ∈ H} d(x) = qh + T`, so

```
q(qh + T) = ∑ q·a(u) ≤ ∑ d(u)·a(u) + ∑ (q − d(u))⁺·a(u) ≤ h(n − 1) + (q − 1)·S ,
```

because a vertex with `d(u) < q` has `a(u) ≤ d(u) ≤ q − 1`. In words: every high-degree
vertex needs `q − ρ` units of degree shortfall in its neighbourhood, and a vertex of degree
`q − s` can serve at most `q − s ≤ q − 1` high-degree vertices, so `(q − 1)S ≥ (q − ρ)T`
(using `h ≤ T`). The other ingredients are the degree identity `2m + S = nq + T` and the chord
sum with its slack, `(2q + 1)·2m + 2S ≤ n(n − 1) + nq(q + 1)` (V004's `chordDef`, summed
over all vertices). Eliminating `S`, `T`, `h` gives `D·2m ≤ D·nq + nρ(ρ − 1)`.

This was found by treating the per-vertex constraints as a linear program in the degree
sequence, as the track report suggested, and solving its relaxation with the overlap
constraint `a(u) ≤ d(u)` by hand: the optimum has all low degrees equal to `q − 1` and all high
degrees equal to `q + 1`, which is what the pointwise estimates above reproduce. Only
`q = ⌊√(n − 1)⌋` is folded in: at `q + 1` the residue `ρ` is `0` and the bound is V002's, at
`q − 1` it exceeds `q` and the bound is worse than V002's.

The bound improves V004 at 876 of the first 2000 values of `n` (first at
`n = 11, 27, 28, 29, 38, …`), by `1` up to `n = 82`, by `2` from `n = 83`, and by `10` at
`n = 1943`. It is consistent with all known exact values (`n ≤ 53`, OEIS A006856, checked
numerically, not used in any proof) and is tight at `n = 11` (`f(11) = 16`).

## How the proofs were obtained

Written by hand by the AI agent, in one file, reusing the four earlier lemmas
(`V001.sum_sq_degree_le`, `V002.chord`, `V003.nbr_sum_le`, `V004.chordDef`):

- `chord_slack`: the pointwise chord with truncated slack `2(q − d)⁺`, one case each from
  `V004.chordDef` and `V002.chord`.
- `sum_nbr_swap`: the double counting, by `Finset.sum_comm` after writing the neighbourhood
  as a filter of `univ`.
- `card_filter_adj_le`: `a(u) ≤ d(u)`, an injection into the neighbourhood.
- `arith`: the final elimination, cast to `ℤ` with `zify` and closed by `nlinarith` after the
  two needed products (`(ρ − 1)·` the chord sum, `ρ·` `h ≤ T`) are supplied by hand.
- `main_ineq`: assembles the four facts for an arbitrary graph of girth `≥ 5`; the sums `S`,
  `T` are taken over all vertices with truncated subtraction, which avoids all filtering
  except for `H` itself.
- `bnd_valid`: the `D = 0` branch is `C(n, 2)`; otherwise `D ≠ 0` forces `ρ ≥ 1` and `q ≥ 1`.

The first build failed only on a `congr` goal split and a case split (`d = q` versus `d < q`)
in the pointwise inequality. The whole file costs 46536 heartbeats (`arith` 29434).

Witness `n₀ = 11`: `17 → 16`, the exact value.

## Setup

- Tools: Claude Fable 5.1 (`claude-fable-5-1`) as an autonomous Claude Code agent; Lean 4 /
  Mathlib as pinned by the project; Python 3.12 for evaluating the bound against V004 and for
  a randomised check of every intermediate inequality on 1200 random graphs of girth `≥ 5`.
- Machine: 96 cores, 755 GB RAM, Linux 6.8.0-124-generic.
- Time spent: about two hours, most of it on the mathematics; the Lean proof took two builds.
- No computation outside Lean enters the proof; the Python scripts only chose the bound and
  the witness.

## Sources

- The per-vertex count and the chord sum are those of V003 and V004 of this track; no outside
  code or data was used. Known values (OEIS A006856) were used only to sanity-check the bound
  numerically.
