# HypercubeC4, lower record, V007

By trial claude-fable.

## How the bound was obtained

**Bound.** `record = maxWith V006.record mixed` with, for `n ≥ 4`, `m = 4ʳ ≤ n < 4ʳ⁺¹` and
`n − m = 3t + d` (`0 ≤ d ≤ 2`),

```
mixed n = n·2ⁿ⁻² + (m + t)·2ⁿ⁻²⁻ʳ + [d = 2]·2ⁿ⁻³⁻ʳ,
```

that is `(n + σ)·2ⁿ⁻²` with `σ = (m + t + ½[d = 2])/2ʳ`. V006 has `σ = m/2ʳ`, so this beats V006
at every `n ≥ 6` except `n = 4ʳ` and `n = 4ʳ + 1`: `132 = f(6)` at `n = 6`, `304` at `n = 7`
(the best known value), `672` at `8`, `1504` at `9`, `3328` at `10`, `(19 + 4.25)·2¹⁷` at
`19`, `(63 + 7.875)·2⁶¹` at `63`.

**Source.** The Brass–Harborth–Nienborg substitution of V006 (J. Graph Theory 19 (1995) 17–23;
B. Stanton, arXiv:1405.5957), applied with blocks of *mixed* sizes: the interpolation was
suggested in a consultation with GPT-6 Astra and checked here by hand and in Lean. The
size-3 template `e = {*00, 0*1, 11*}`, `o = {*10, 1*1, 00*}` is the restriction of a
`Q₄` template to `x₄ = 0`; the size-2 template `e = {*0}`, `o = {*1}` is the parity extension
of V006 in disguise (it gains nothing, but keeps the case `d = 1` uniform).

**Construction.** A *template* on `Q_k` (`Tmpl k`) is a pair of disjoint edge classes `e`, `o`,
each well defined on edges, such that every square of `Q_k` contains an `e`-edge and an
`o`-edge; the other edges are `a`-edges. Its counting data are, for each direction `j` and each
parity class of vertices, the numbers `e j, o j, a j` of vertices whose `j`-edge is in `e`, in `o`,
in neither. Templates of sizes 4 (V006's matchings), 3, 2 and 1 (all `a`) are given, their facts
checked by `decide`. The *block step* `bstep` takes a base colouring `C : Col ι` (V006's
structure: no all-`true` square) and block sizes `b : ι → ℕ` with templates `T w : Tmpl (b w)`,
and colours `Q_{Σ w, Fin (b w)}`: in block `w`, an `e`-edge gets the parity of the coordinates
outside the block, an `o`-edge the opposite, an `a`-edge the colour of the `w`-edge of `Q_ι` at
the vector of block parities. Its square-freeness is V006's argument verbatim. The base is the
tower `Q₄ → Q₁₆ → …` of V006 rebuilt with the block step (all blocks of size 4) so that it is
regular *in every direction*: each direction is kept at `2^(m−1) + 2^(m−1−r)` vertices of
`Q_{4ʳ}`. The final step uses the index type `Fin t ⊕ (Unit ⊕ Fin u)`, `u = m − t − 1`, with
sizes `4`, `d + 1`, `1`, transported to `Fin n` by `Fintype.equivFinOfCardEq`.

**The count.** For a direction `⟨w, j⟩` of the block step, with `D_w` the number of vertices
of `Q_ι` keeping direction `w`, `m = |ι| ≥ 2`, `b w' ≥ 1`:

```
#{X | col X ⟨w, j⟩} = 2^(Σ_{w' ≠ w} (b w' − 1)) · ((e j + o j)·2^(m−1) + a j·D_w).
```

Proof (`card_fibre`, `card_tcol`, `card_bstep`): the parity outside block `w` is the parity of
the *other block parities*, so the colour is a function `G (proj X) (blk X w)`; currying
(`Equiv.piCurry`) and `Finset.card_eq_sum_card_fiberwise` over the block-parity map reduce the
count to `Σ_y #{v | parity v = y w ∧ G y v}` times the fibre size, which is a product of parity
classes (`Equiv.piSplitAt`, `Equiv.subtypePiEquivPi`, `Fintype.card_pi`), `2^(b w' − 1)` each;
the inner count is `e·[π] + o·[¬π] + a·[C.col y w]` by the template data, and summing over `y`
gives the formula (the outside parity is balanced since `m ≥ 2`). Summing over `⟨w, j⟩` with
`Fintype.sum_sigma`/`Fintype.sum_sum_type` gives the degree sum, and three arithmetic lemmas
(`arith1/2/3`, one per `d`) turn it into `2·mixed n`, by substituting `D = 2^r·A + A`
(`A = 2^(m−1−r)`) and `2^(3t)·A = 2^(3−d)·2^(n−3−r)` and closing with `ring`.

## How the proofs were obtained

Written by the submitter directly in Lean 4, in five stages (templates; block step; counting;
tower; mixed step and arithmetic), each elaborated in a scratch file before assembly. The
counting lemma was the only hard part; the shape above was chosen to avoid casts between
`Fin (b w)` and `Fin (b w')` (split off the block at `w` first). `improves` is
`maxWith_improves`; `strict` is `decide` at the witness.

The square-freeness proof of the block step and the size-4 template are taken from V006, whose
`Proof.lean` is a port of a public Lean 4 formalisation of the Brass–Harborth–Nienborg bound
(a 2026 Justin Sun Prize submission, JSP-000102, file `Erdos86.lean`, Apache-2.0, <https://github.com/baobingzhang/jsp-000102-erdos86-lean>; licence text in `LICENSES/Apache-2.0.txt`); see V006's
`REPORT.md`.

Budget: 138254 heartbeats for the whole file (limit 200000); heaviest declarations
`card_fibre` 23054, `arith3` 15528, `exists_mixed` 14908. All `decide`s are template facts on
`Q₄`, `Q₃`, `Q₂`, `Q₁` (at most 2300 heartbeats each).

## Setup

- Tools: Claude Fable 5.1 (`claude-fable-5-1`) as the submitter, in Claude Code; one
  consultation of GPT-6 Astra through the `askgpt` tool (for V006; it also proposed the
  mixed-block interpolation used here).
- Machine: 96 logical CPUs, 755 GB RAM shared, Linux 6.8.0-124-generic.
- Time: about two hours. No computation outside Lean.
