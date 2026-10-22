# HypercubeC4, lower record, V008

By the SqueezeBench maintainers, trial claude-fable.

**Verification.** The proof builds without `sorry`, but `squeeze verify` first rejected it at
the Comparator gate ("exceeded 16384 MB of memory"). The maintainers traced it to one glue
lemma, `le_f_eight`: nanoda, the Comparator's second kernel, evaluated the closed edge count
`#(mgraph M8).edgeFinset` by unfolding the decidable adjacency test over the 256 vertices,
which Lean's kernel never does, and needed 45 GB; the bitwise operations on the 256-bit masks
were not the cause. The lemma is now proved for an arbitrary certificate `M` (`le_f_eight_of`)
and instantiated with `M8`, so no closed term can be evaluated. With that change `squeeze
verify` accepts the record under the standard limits in about 80 seconds.

## How the bound was obtained

**Bound.** `record = patch V007.record 8 682`: the single value `f(8) ≥ 682` (V007 gives 672).

**Source.** The 682-edge subgraph of `Q₈` is the "odd-square" witness of Minamoto,
*C₄-free subgraphs of the hypercubes Q₆, Q₇ and Q₈: odd squares, fully frustrated models, and
computational structure* (revision of arXiv:2603.29127, 2026; repository file
`q8_odd_square_682.json`, MIT licence), which attains the value reported by Marinari, Parisi
and Ritort, *J. Phys. A* 28 (1995) 327, for the ground state of the fully frustrated Ising model
on `Q₈`. The graph is the set of satisfied bonds of a spin configuration for the canonical fully
frustrated coupling `J(x, x ⊕ 2ⁱ) = (−1)^{popcount(x mod 2ⁱ)}`: every square has an odd number
of negative couplings, so every square has an odd number of unsatisfied bonds, and the
satisfied bonds contain no square. The same value (and the same graph up to symmetry) is
found in a fraction of a second by simulated annealing on the 256 spins (a small C program,
written for this record; see the track report for its use at larger `n`).

**Certificate.** The graph is given as eight 256-bit numbers `M0 … M7`: bit `c` of `Mᵢ` is set
iff the edge `{c, c ⊕ 2ⁱ}` is kept (`c` the word read as a binary numeral). `mgraph M` is the
subgraph of `hypercube 8` with these edges (an edge is kept when the bits at both of its ends
are set, so the graph is symmetric by construction), and three facts are settled by
`decide +kernel`, all GMP-accelerated `Nat.testBit` evaluations: the masks are symmetric
(`M8_sym`), no square has all four bits set (`M8_sq`, 256 words × 56 ordered direction pairs),
and the popcounts sum to `2·682` (`M8_count`, by a structural recursion `pc` on the bit count).

## How the proofs were obtained

Written by Fable 5.1 directly in Lean 4. The reusable part (`code`, `decode`, `testBit_code`,
`code_flip`, `card_code`, `pc`, `card_testBit_range`, `mgraph`, `mgraph_not_hasSquare`,
`mgraph_two_mul_card_edges`) turns any family of symmetric bitmasks into a subgraph of the
cube with a square-freeness criterion and an edge count in terms of `testBit`, so that later
records can patch in further small-`n` graphs found by search. `improves` and `strict` are
`decide`/`decide +kernel` at `n = 8`.

Budget: 19509 heartbeats for the whole file; heaviest `testBit_A` at 4307.

## Sources

- Minamoto, *C₄-free subgraphs of the hypercubes Q₆, Q₇ and Q₈: odd squares, fully frustrated
  models, and computational structure*, arXiv:2603.29127 (2026 revision); the file
  `q8_odd_square_682.json` of its repository, MIT licence. Used as data: the 682-edge graph,
  re-encoded as the masks `M0 … M7`.
- Marinari, Parisi and Ritort, *J. Phys. A* 28 (1995) 327: the value 682 as the ground-state
  energy of the fully frustrated Ising model on `Q₈`. Citation only.
- Code reused from earlier versions is listed in `based-on`.

## Setup

- Tools: Claude Fable 5.1 (`claude-fable-5-1`) as the submitter, in Claude Code; one
  consultation of GPT-6 Astra (literature on fully frustrated hypercubes).
- Machine: 96 logical CPUs, 755 GB RAM shared, Linux 6.8.0-124-generic.
- Time: about one hour. Computation outside Lean: a Python check of the published edge list
  (symmetry, squares, count) used to produce the masks; the simulated annealing program was
  run for confirmation only.
