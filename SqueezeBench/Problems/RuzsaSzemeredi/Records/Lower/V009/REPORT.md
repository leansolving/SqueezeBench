# RuzsaSzemeredi, lower record, V009

By Pablo Manrique.

## The bound

With `R8 = V008.record`:

```
tb n     = R8 n                                                    for n < 15
tb n     = max ( R8 n , 15 , 90 · tb ⌊n/15⌋ , [n ≥ 27] max(45, 270 · tb ⌊n/27⌋) )   otherwise
sAux k n = max ( tb n , max over 1 ≤ j ≤ k of  tb (n - n mod 3^j) + tb (n mod 3^j) )
record n = sAux ⌊log₃ n⌋ n
```

(In `Def.lean`, `tb n := tAux n n` is computed by fuel recursion; the fuel `n` exceeds the
recursion depth, which is at most `log₁₅ n`, so it never runs out.)

**Witness.** `n₀ = 15`: `V008 = 10 → V009 = 15` (the Kneser graph `KG(6,2)`). Upper V008 is
`15` at `n = 15` and `45` at `n = 27`, so with V009 the two records determine `f(15) = 15` and
`f(27) = 45`.

## How the bound was obtained

Two operations on locally linear graphs, and two small graphs that the group constructions of
V001–V008 (Ruzsa–Szemerédi tripartite graphs over `F₃^k × Z_N`, Cayley graphs of symmetric caps)
do not produce.

1. **Tensor product: `f(a·b) ≥ 6·f(a)·f(b)`.** For graphs `G`, `H` let `G × H` have
   `(x, y) ~ (x', y')` iff `x ~ x'` and `y ~ y'`. A graph is locally linear iff every edge has
   exactly one common neighbour; the common neighbours of an edge of `G × H` are the pairs of
   common neighbours of its two projections, so `G × H` is locally linear. Degrees multiply, so
   `e(G × H) = 2 e(G) e(H)`, and since `e = 3t` in a locally linear graph,
   `t(G × H) = 6 t(G) t(H)` (each pair of triangles gives `3! = 6` triangles).
2. **Disjoint union: `f(a+b) ≥ f(a) + f(b)`.**
3. **`KG(6,2)`** (15 vertices: the 2-subsets of a 6-set, adjacent iff disjoint; triangles = the 15
   perfect matchings of `K₆`; it is the collinearity graph of the generalized quadrangle
   `GQ(2,2)`, SRG(15,6,1,3)): `f(15) ≥ 15`, where V008 has `10`.
4. **The collinearity graph of `GQ(2,4)`** (the complement of the Schläfli graph, SRG(27,10,1,5)):
   the intersection graph of the 27 lines on a smooth cubic surface, `a₁…a₆, b₁…b₆, c_ij`, with
   `aᵢ ~ bⱼ` (`i ≠ j`), `aᵢ, bᵢ ~ c_ij`, `c_ij ~ c_kl` (`{i,j} ∩ {k,l} = ∅`); its 45 triangles are
   the tritangent planes `{aᵢ, bⱼ, c_ij}` (30) and `{c_ij, c_kl, c_mn}` (15). `f(27) ≥ 45`, where
   V008 has `36`.

At `n = 15` and `n = 27` the upper record V008 evaluates to `15` and `45`, so
`f(15) = 15` and `f(27) = 45` are now settled by the two records. Their value as tensor factors comes from
`g(n) = 6 f(n)/n`, which is multiplicative under the product: `g = 6` at `n = 15` and `g = 10` at
`n = 27`, against `g = 4` at `9` and `g = 8` at `27` for the cap constructions. In particular for
every `j ≥ 1`, at `n = 15 · 3^j` the record is at least `90 · V008(3^j)`, and the gain over V008
there lies between `1.2` and `1.5` for every `j ≤ 15` (Python model). The gains appear to repeat
with period 6 in `j`, following the cap sizes, which would give an infinite family with a gain
of at least `1.2`; this is observed numerically, not proved. `GQ(2,4)` gains `1.25` at
`n = 27 · 729^q` (`10` against `symr 3 = 8`).

The tensor product with V008 itself gave nothing in a numerical test (`n < 20000`), and neither
did more split moduli (`2·3^k`, at large `n`), so the record uses just the two small factors and
splits by powers of three. The split fills the flat stretches of V008's step function (e.g.
`n = 1000`: `13608 → 15228 = f(729) + f(271)`).

**Comparison with V008** (Python model of V008 and V009; it reproduces the `#eval` of both records in
Lean at all 21 points of the table below):

* `3 ≤ n < 20000`: V009 > V008 at **98.7%** of all `n`; average gain where better `×1.13`, maximum
  `×1.53` (`n = 12150`). The tensor part alone beats V008 at 51% of these `n`, up to `×1.5`.
* `10^5 ≤ n < 1.1·10^5`: V009 > V008 at **every** `n`, average gain `×1.16`, maximum `×1.20`.

| n | 15 | 18 | 27 | 45 | 225 | 249 | 405 | 501 | 603 | 1000 | 1461 | 10005 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| V008 | 10 | 10 | 36 | 60 | 1050 | 1620 | 2700 | 3674 | 5460 | 13608 | 21428 | 631800 |
| V009 | **15** | **15** | **45** | **90** | **1350** | **1621** | **4050** | **4065** | **5715** | **15228** | **24301** | **635904** |

Unchanged in this sample: `n = 9, 21, 57, 81, 165, 195, 243, 729, 2187` (powers of three and
some tripartite optima).

| n = 15·3^j | 15 | 45 | 135 | 405 | 1215 | 3645 | 10935 | 32805 | 98415 | 295245 | 885735 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| V008 | 10 | 60 | 450 | 2700 | 16200 | 109350 | 816480 | 4920750 | 36741600 | 220449600 | 1322697600 |
| V009 | 15 | 90 | 540 | 4050 | 24300 | 145800 | 1224720 | 7348320 | 44089920 | 330674400 | 1984046400 |

## How the proofs were obtained

Written by an AI agent (see *Setup*), by hand-style reasoning; no proof search beyond Lean's
standard tactics.

* `Ops` (general, reusable): `common_of_ll` / `ll_of_common` (locally linear ⇔ every edge has
  exactly one common neighbour), `tensor` and `dsum` with their local linearity, edge counts via
  `sum_degrees_eq_twice_card_edges`, and triangle counts via Mathlib's
  `LocallyLinear.card_edgeFinset`. `six_mul_le` and `add_le` apply them to extremal graphs from
  Mathlib's `ruzsaSzemerediNumber_spec`. The pattern of `ll_of_common` (a 3-clique through `x, y`
  is `{x, y, z}` by `eq_of_subset_of_card_le`) is adapted from V007's `CayleyCap.triangle_eq`.
* `Mask`: a graph on `Fin n` is one `n²`-bit natural number. `MaskOk` (irreflexive, symmetric,
  and for each edge `xy` the common neighbours `z < n` are exactly `thd x y`, the top bit of the
  meet of the two rows) and the degrees are checked by `decide +kernel`. This is a check of supplied
  data, not a search: at most `n³` bit lookups (`6746` heartbeats for `GQ(2,4)`). The masks were
  generated by a short Python script from the descriptions above; the script also checked local
  linearity and the triangle counts independently.
* `tAux_le`, `sAux_le`: induction on the fuel, with `step_le` (`f n ≥ 6 · T · f ⌊n/a⌋` from
  `T ≤ f a`) and `add_le`. `improves` holds because every branch of `tAux` contains `V008.record n`.
  `strict` is `decide +kernel` at `n = 15`.

Problems hit: `SimpleGraph.loopless` is now `Std.Irrefl` (use `G.irrefl`); `rw [← card_map …]`
rewrote the wrong `card`, fixed by stating the neighbour-finset equality first; `Finset.sum_mul_sum`
had to be instantiated explicitly.

**Budget.** `budget-probe`: whole file `40441` heartbeats; largest declarations `MGQ_ok` 6746,
`dsum_card_edges` 4575, `six_mul_le` 4528, `add_le` 4149. Kernel evaluation of the record
(scratch probe): `V008.record 15 < V009.record 15` 977 heartbeats, `n = 81, 99, 100` 4331–5032,
`n = 1000` 24967; all far below the fuel budget of 200000.

## What the next improvement would take

* **More sporadic factors.** Any locally linear graph with a better `g = 6t/n` than the record's
  at its size is a new tensor factor. The Cossidente–Penttila graph SRG(378,52,1,8) has
  `3276` triangles on `378` vertices, against V009's `2340` there; it would need a structured
  description (it comes from a hemisystem of a Hermitian surface, Cossidente–Penttila 2005),
  since a mask check of `378³ ≈ 5.4 · 10⁷` bit lookups is beyond the budget.
* **Exact small values as factors.** The README's exhaustive values `f(12) = 9`, `f(13) = 10`
  (both above the record) would, as further tensor factors, raise the share of `n < 20000` where
  the tensor part alone beats V008 from 51% to 63% (Python model); they need explicit graphs.
* The items of the track report (caps in `F₃^7`, Behrend) are unaffected and still apply.

## Sources

No outside code. Mathematical data, used with citation:

* The Kneser graph `KG(6,2)` / `GQ(2,2)` and the collinearity graph of `GQ(2,4)` (27 lines on a
  cubic surface, 45 tritangent planes): classical; see A. E. Brouwer, H. Van Maldeghem,
  *Strongly Regular Graphs*, Encyclopedia of Mathematics and its Applications, Cambridge
  University Press 2022 (SRG(15,6,1,3) and SRG(27,10,1,5)), and S. E. Payne, J. A. Thas,
  *Finite Generalized Quadrangles*, 2nd ed., EMS Series of Lectures in Mathematics 9, EMS Press
  2009, doi:10.4171/066.
* The Cossidente–Penttila graph, mentioned only as a possible next step: A. Cossidente,
  T. Penttila, *Hemisystems on the Hermitian surface*, J. London Math. Soc. (2) 72 (2005),
  731–741.
* The list of locally linear strongly regular graphs (including Cossidente–Penttila) was looked
  up in Wikipedia, *Locally linear graph*, https://en.wikipedia.org/wiki/Locally_linear_graph
  (accessed 2026-10-01; CC BY-SA 4.0), only for orientation; nothing was copied.
* Mathlib (Apache-2.0) is used as a library, not copied.

## Setup

- Tools: Claude Opus 5.5 (`claude-opus-5-5`) as an autonomous agent in Claude Code, Lean 4
  (v4.31.0, the pinned toolchain) with Mathlib, Python 3 for generating the masks and for a
  numerical model of the records V008 and V009.
- Machine: Linux 6.8.0-124-generic, a shared server (`nproc` 96, 755 GB RAM); this session was
  limited to 4 CPUs and 20 GB of memory.
- Time: about 40 minutes of a 120-minute session. Computation outside Lean: the mask generation
  and its independent check (seconds), and the comparison of V008 and V009 over `n < 20000` and
  `10^5 ≤ n < 1.1·10^5` (under a minute). No search found any construction; both graphs are
  classical.
