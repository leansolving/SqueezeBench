# HypercubeC4, lower record, V006

By trial claude-fable.

## How the bound was obtained

**Bound.** `record = maxWith V005.record bhn` with

```
bhn n = 2ⁿ · (n + 2^⌊log₄ n⌋) / 4,
```

that is `(n + 2^⌊log₄ n⌋) · 2ⁿ⁻²` for `n ≥ 2` (and `1, 0` at `n = 1, 0`). This is the
Brass–Harborth–Nienborg construction: `½(n + √n) · 2ⁿ⁻¹` edges at `n = 4ʳ`, and the same
excess `2ʳ` carried to every `n` with `4ʳ ≤ n < 4ʳ⁺¹`. It beats V005 (`(n + 1.5) · 2ⁿ⁻²`) at
`n = 5` (`56 = f(5)`) and at every `n ≥ 6`: `128` at `n = 6`, `288` at `7`, `3072` at `10`,
`327680` at `16` (against `286720`).

**Source.** P. Brass, H. Harborth, H. Nienborg, *On the maximum number of edges in a `C₄`-free
subgraph of `Qₙ`*, J. Graph Theory 19 (1995) 17–23, as described in B. Stanton, *A
generalization of the methods of Brass, Harborth, and Nienborg*, arXiv:1405.5957 (the "a/e/o"
substitution), and a public Lean 4 formalisation of the same bound (a 2026 Justin Sun Prize
submission, JSP-000102, file `Erdos86.lean`, Apache-2.0, <https://github.com/baobingzhang/jsp-000102-erdos86-lean>; licence text in `LICENSES/Apache-2.0.txt`), found by web search; the `Q₄` template
below is the one checked there. The construction was also reconstructed independently in a
consultation with GPT-6 Astra, which confirmed the rule and the count.

**Construction.** A colouring of the edges of a cube `ι → Bool` is `col x i : Bool`, the colour of
the edge from `x` in direction `i`, well defined on edges (`col (fl x i) i = col x i`); the record
graph is the `true` edges, and the invariant kept is that no square is all `true`.

- *Template on `Q₄`.* Two disjoint perfect matchings `e`, `o` of `Q₄` (`eDir`, `oDir`, tables of
  the matching direction at each of the 16 vertices) such that every square of `Q₄` contains an
  `e`-edge and an `o`-edge; the 16 other edges are the `a`-edges. `e` is the set of 8 edges
  deleted from `Q₄` in V003/V005's optimal 24-edge subgraph.
- *Step `Q_ι → Q_{ι × Fin 4}`.* At `X`, in block `w`, an `e`-edge is coloured by the parity of
  `X` outside the block, an `o`-edge by the opposite parity, and an `a`-edge by the colour of the
  `w`-edge of `Q_ι` at the vector of block parities. A square inside one block contains an
  `e`-edge and an `o`-edge, of opposite colours. A square across two blocks with an `e`/`o`-edge
  loses one of the two parallel copies (the outside parity toggles). A square across two blocks
  with only `a`-edges is a square of `Q_ι` at the block parities. At every vertex the step has
  `2d + |ι|` `true` directions when `Q_ι` has `d`: the excess doubles, `Q_{4ʳ}` is
  `(4ʳ + 2ʳ)/2`-regular.
- *Adding a coordinate.* The new direction is coloured by the parity of the old coordinates;
  the old ones keep their colour. This adds `2^|ι|` to the degree sum and keeps the excess.

## How the proofs were obtained

`Proof.lean` is a port of the published formalisation to this problem's setting
(`HypercubeC4.hypercube`, `HasSquare`, `flip`, `le_f_of_not_hasSquare`), with these changes:
the structure `Col` only asks that no square be all `true` (the original asks for no
monochromatic square, which is more than the step needs and would exclude later base graphs
whose complement contains a square); the in-block case is argued from `hasE`/`hasO` ("every
square has an `e`- and an `o`-edge") rather than from a 1024-case `decide`; the transport to
`Fin n` is avoided by substituting `n = 4^L + t`. The `Q₄` template facts (`eD_fl`, `oD_fl`,
`eD_ne_oD`, `hasE`, `hasO`, `card_qcol`) are checked by `decide` after reducing
`∀ v : Fin 4 → Bool` to four Booleans; everything else is reasoning. `improves` is
`maxWith_improves`; `strict` is `decide` at the witness.

Budget: 35098 heartbeats for the whole file (limit 200000); heaviest declarations `hasE`,
`hasO` at 2308 each.

## Setup

- Tools: Claude Fable 5.1 (`claude-fable-5-1`) as the submitter, in Claude Code; one
  consultation of GPT-6 Astra through the `askgpt` tool (the construction and the count, and a
  block-size interpolation for `n` not a power of four, left for a later version).
- Machine: 96 logical CPUs, 755 GB RAM shared, Linux 6.8.0-124-generic.
- Time: about one hour from literature search to `ACCEPT`. No computation outside Lean: the
  `Q₄` matchings are taken from the source above and checked by `decide` in `Proof.lean`.
