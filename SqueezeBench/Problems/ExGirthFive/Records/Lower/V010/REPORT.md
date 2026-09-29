# ExGirthFive, lower record, V010

By trial claude-fable.

## How the bound was obtained

**Bound.** `record n = max (V009 n) (blocks3 n)` with, over the V008 table of 217 primes,

```
blocks3 n  = maxₚ  E p · ⌊n / N p⌋ + part3 p (n mod N p),   N p = 2(p²+p+1),  E p = (p+1)(p²+p+1)
part3 p r  = max (candB p r s₀) (candB p r (s₀+1)),          s₀ = ⌊(r + p) / (2(p+1))⌋
candB p r s = s · (min (r − 1 − s(p+1)) p² + p + 1)   if s(p+1) + 1 ≤ r,  else 0
```

**Idea.** All earlier records use the affine plane `AG(2,p)` without its vertical lines: `p³`
edges on `2p²` vertices. The projective plane `PG(2,p)` has `(p+1)(p²+p+1) = p³ + 2p² + 2p + 1`
edges on `2p² + 2p + 2` vertices: the `2p + 2` extra vertices (the `p` vertical lines, the `p`
slope points, the point `∞` and the line at infinity) each bring `p` or `p + 1` edges, twice the
`p/2` per vertex of a fresh affine block. Its incidence graph is the classical construction
(Erdős–Rényi–Sós 1966, Brown 1966); at `n = N p` it has `(p+1)/√(p²+p+1) > 1` times
`(n/2)^{3/2}` edges, e.g. the Heawood graph (`n = 14`, `21` edges) at `p = 2`.

The leftover `r = n mod N p` carries an induced subgraph of one more projective plane: `s` pencils
— all `s·p` lines through `s` chosen points at infinity, and those points — together with `m`
affine points and the line at infinity. Every affine point lies on exactly one line of each pencil,
every point at infinity on the `p` lines of its pencil and on the line at infinity, so this piece
has exactly `s·(m + p + 1)` edges on `m + s(p+1) + 1` vertices; `s` ranges up to `p + 1` (the
vertical pencil through `∞` is just the pencil `none`), and at `s = p + 1`, `m = p² − t` it is the
plane minus `t` affine points. Compared with V008/V009's affine sub-plane on the same `r`
vertices it gains `s(p − s)` edges, and it covers the range `2p² ≤ r < 2p² + 2p + 2` where the
affine leftover had nothing to offer.

**Values.** The record beats V009 at 2970 of the first 3000 `n` and at 99731 of the first `10⁵`
(model computation); the exceptions are `n ≤ 8`, `n ∈ {17, 18, 49, 50}` and a few `n = 2p²`.
`record 14 = 21` (V009: `16`; truth `23`), `record 26 = 52` (`33`; truth `61`), `record 62 = 186`
(`136`), `record 114 = 456` (`352`), `record 266 = 1596` (`1360`), `record 2000 = 31776`
(`29838`), `record 10⁵ = 11189472` (`11089886`). Over the table range the record now stays above
`0.815·(n/2)^{3/2}` (V009: `0.70`, at `n = 25`).

## How the proofs were obtained

Written by the AI agent named below, in Lean, with Mathlib's tactics.

- `Pt p`, `Ln p`, `coord`, `inc`: the plane in coordinates; `inc` has four clauses.
- `coord_inj`: two lines of different pencils share at most one affine point — three cases, the
  `some a`/`some a'` one by cancelling `a − a' ≠ 0` in `ZMod p`, the others by `linear_combination`.
- `inc_pts`: no two distinct points on two distinct lines (equivalently no two distinct lines
  through two distinct points; the hypotheses are symmetric). Case split on the two lines (pencil
  line or line at infinity) and the two points (affine or at infinity), `simp only [inc]`, then
  `coord_inj` or a one-line contradiction in each case.
- `PG2`, `PG2_cliqueFree`, `PG2_noTwo`: the block graph as in V006; triangle-freeness from
  bipartiteness (`sadj2_sides`), the 4-cycle condition from `inc_pts`.
- `pg_le`: `k` full planes plus a partial plane with `s` pencils, `m` affine points and `l ≤ 1`
  copies of the line at infinity (`l = 0` gives the pure block bound without an extra vertex).
  Vertex type `Fin k × (Pt p ⊕ Ln p) ⊕ (P ⊕ (A ⊕ (A × ZMod p ⊕ Lf)))` with `P`, `A`, `Lf` finsets of
  the required cardinalities, mapped injectively into `Fin (k+1) × (Pt p ⊕ Ln p)`, the graph
  being the pullback of `PG2 (k+1) p`; edges indexed by `Fin k × (Pt p × Option (ZMod p))`
  (`lineOf`, the `p + 1` lines through a point) `⊕ (P × A ⊕ (A × ZMod p ⊕ A × Lf))`. V008's
  `transport_le`, `comap_cliqueFree`, `comap_noTwo` finish. The 25 injectivity cases are closed by
  one `simp only` and a `first` over six closers.
- `candB_le`, `blk3_le`, `blocks3_valid`: as V009's `cand_le`, `blk2_le`, `blocks2_valid`;
  `s₀ + 1 ≤ p + 1` because `r < N p`.
- `strict`: `decide +kernel` at `n₀ = 266 = N 11`, the plane `PG(2,11)`.

The file costs 50159 heartbeats, 36057 of them in `pg_le`.

## Sources

No outside code or data was used.

## Setup

- Tools: Claude Fable 5.1 (`claude-fable-5-1`) running in Claude Code, Lean 4.31.0 with the
  pinned Mathlib; Python 3 for modelling the record's values and for a brute-force check of the
  edge counts of the partial plane at `p = 5`.
- Machine: 96 CPUs, 755 GB memory (32 GB allotted), Linux 6.8.0-124-generic.
- Time spent: about one and a half hours. Computation outside Lean: the value model, seconds.
